"""Structural featurization and clustering of programs.

Two things live here, both built on the same *structural view* of a program:

* ``structural_features`` — a TF-IDF vector over normalized-AST path n-grams.
  Identifiers and literals are folded to their node type (as in the RPS labeler),
  so two programs are close when they have the same *shape*, regardless of names.

* ``cluster`` — group a set of programs by that view and return, per cluster, a
  medoid (the most central real program).

The structural view still ranks transplant candidates. Build-sample selection
and the fallback's reference pick both moved to the BFS edit view below, which
asks what a program has to *change* rather than what it looks like.
"""
from __future__ import annotations

import ast
from collections import deque
from dataclasses import dataclass

import numpy as np
from Levenshtein import editops
from rapidfuzz.distance import Levenshtein as _RFLev
from rapidfuzz.process import cdist as _rf_cdist
from scipy.optimize import linear_sum_assignment
from sklearn.cluster import AgglomerativeClustering
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics import pairwise_distances


# --------------------------------------------------------------- featurization
def _node_label(node: ast.AST) -> str:
    """Node type, with names/literals folded away (shape, not identity)."""
    return type(node).__name__


def _paths(node: ast.AST, prefix: tuple[str, ...], out: list[str], depth: int) -> None:
    """Root-to-node label paths of length <= 3, as underscore-joined tokens."""
    label = _node_label(node)
    path = (prefix + (label,))[-3:]
    out.append("_".join(path))
    for child in ast.iter_child_nodes(node):
        _paths(child, path, out, depth + 1)


def ast_paths(source: str) -> str:
    """Space-joined AST path n-grams for one program; '' if it does not parse."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return ""
    out: list[str] = []
    _paths(tree, (), out, 0)
    return " ".join(out)


def structural_features(sources: list[str]):
    """TF-IDF matrix over AST path n-grams. Returns (matrix, vectorizer)."""
    docs = [ast_paths(s) for s in sources]
    # lowercase=False: the tokens are AST node type names, and folding their case
    # is at best a no-op and at worst silently merges two distinct types.
    vec = TfidfVectorizer(token_pattern=r"[^\s]+", min_df=1, lowercase=False)
    # guard: all-empty corpus (all unparseable) would raise
    if not any(docs):
        return np.zeros((len(sources), 1)), None
    matrix = vec.fit_transform(docs)
    return matrix, vec


# --------------------------------------------------------------- BFS edit view
# A second view of a program, used to pair it with a correct solution and to
# describe the repair that pairing implies. Where ``ast_paths`` describes what a
# program *looks like*, this describes what has to *change*: the buggy program
# and its partner are each flattened to one breadth-first node-type sequence per
# top-level definition, matched one-to-one, and the Levenshtein alignment
# between matched sequences is read out as edit operations. Clustering those
# operations groups programs by the transformation that repairs them, which is
# the partition a build sample has to respect -- a rule induced from a
# representative only pays off on members needing the same edit.
_NODE_CHAR: dict[str, str] = {}


def _char(name: str) -> str:
    """One stable character per AST node type, so Levenshtein can run in C."""
    if name not in _NODE_CHAR:
        _NODE_CHAR[name] = chr(0x100 + len(_NODE_CHAR))
    return _NODE_CHAR[name]


def _label(node: ast.AST, values: bool) -> str:
    """Node type, optionally carrying the identifier or literal it holds.

    Names and literals are folded away by default: two programs that differ
    only in variable naming should look identical. ``values=True`` unfolds them
    for the fallback below, where the fold is exactly what hides the bug.
    """
    kind = type(node).__name__
    if not values:
        return kind
    if isinstance(node, ast.Name):
        return f"Name:{node.id}"
    if isinstance(node, ast.Constant):
        return f"Const:{node.value!r}"
    if isinstance(node, ast.arg):
        return f"arg:{node.arg}"
    if isinstance(node, ast.Attribute):
        return f"Attr:{node.attr}"
    return kind


def bfs_lists(source: str, values: bool = False) -> list[tuple[str, list[str]]]:
    """(encoded, node-type list) per depth-1 child of Module, in BFS order.

    One sequence per top-level definition, so a three-function submission
    yields three; matching them one-to-one is what lets two programs be
    compared when they define the same things in a different order.
    """
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    out: list[tuple[str, list[str]]] = []
    for top in ast.iter_child_nodes(tree):
        names: list[str] = []
        q: deque = deque([top])
        while q:
            node = q.popleft()
            names.append(_label(node, values))
            q.extend(ast.iter_child_nodes(node))
        out.append(("".join(_char(n) for n in names), names))
    return out


def _match(bl: list, cl: list, cost: np.ndarray | None = None):
    """One-to-one assignment of two programs' sequences, minimizing edit cost."""
    if cost is None:
        cost = np.array([[_RFLev.distance(b, c) for c, _ in cl] for b, _ in bl],
                        dtype=float)
    rows, cols = linear_sum_assignment(cost)
    return rows, cols, cost


def bfs_distance(bl: list, cl: list, cost: np.ndarray | None = None) -> float:
    """Total edit distance: matched sequences aligned, unmatched ones charged
    their full length, so a missing or surplus definition costs what it is."""
    if not bl or not cl:
        return float(sum(len(n) for _, n in bl) + sum(len(n) for _, n in cl))
    rows, cols, cost = _match(bl, cl, cost)
    total = float(cost[rows, cols].sum())
    total += sum(len(bl[i][1]) for i in range(len(bl)) if i not in set(rows.tolist()))
    total += sum(len(cl[j][1]) for j in range(len(cl)) if j not in set(cols.tolist()))
    return total


def _ops(bl: list, cl: list, prefix: str = "") -> list[str]:
    """Edit operations between matched sequences, one token each."""
    toks: list[str] = []
    rows, cols, _ = _match(bl, cl)
    for i, j in zip(rows.tolist(), cols.tolist()):
        src, dst = bl[i][1], cl[j][1]
        for op, a, b in editops(bl[i][0], cl[j][0]):
            if op == "replace":
                toks.append(f"{prefix}sub:{src[a]}>{dst[b]}")
            elif op == "delete":
                toks.append(f"{prefix}del:{src[a]}")
            else:
                toks.append(f"{prefix}ins:{dst[b]}")
    for i in range(len(bl)):
        if i not in set(rows.tolist()):
            toks.append(f"{prefix}delfunc:" + "_".join(bl[i][1][:3]))
    for j in range(len(cl)):
        if j not in set(cols.tolist()):
            toks.append(f"{prefix}insfunc:" + "_".join(cl[j][1][:3]))
    return toks


def edit_script(buggy: str, fixed: str) -> str:
    """The repair one program needs, as a bag of edit-operation tokens.

    Node types alone cannot see a wrong or misspelled identifier, or a wrong
    constant: both sides are just ``Name`` or ``Constant``. On two of our
    assignments that blind spot silently empties one submission in eight, and
    an empty script makes every such program a single indistinguishable
    cluster. When the structural script comes out empty, fall back to a
    value-level alignment, which sees exactly those bugs and nothing else.
    """
    bl, cl = bfs_lists(buggy), bfs_lists(fixed)
    if not bl or not cl:
        return ""
    toks = _ops(bl, cl)
    if not toks:
        toks = _ops(bfs_lists(buggy, values=True), bfs_lists(fixed, values=True),
                    prefix="v.")
    return " ".join(toks)


def pair_by_bfs(buggy: list[str], correct: list[str]) -> tuple[np.ndarray, np.ndarray]:
    """For each buggy program, the index of its minimum-edit correct partner.

    Returns ``(index, distance)``. Every pairwise sequence distance is computed
    once in C and the per-program cost matrices are read off as slices; without
    that this is hours rather than seconds on the larger pools.
    """
    B = [bfs_lists(s) for s in buggy]
    C = [bfs_lists(s) for s in correct]
    if not correct:
        return np.zeros(len(buggy), dtype=int), np.full(len(buggy), np.inf)

    bo, co = [0], [0]
    for lists in B:
        bo.append(bo[-1] + len(lists))
    for lists in C:
        co.append(co[-1] + len(lists))
    flat_b = [enc for lists in B for enc, _ in lists]
    flat_c = [enc for lists in C for enc, _ in lists]
    D = (_rf_cdist(flat_b, flat_c, scorer=_RFLev.distance, workers=-1)
         if flat_b and flat_c else np.zeros((0, 0)))

    best = np.zeros(len(buggy), dtype=int)
    dist = np.zeros(len(buggy))
    for i in range(len(buggy)):
        if not B[i]:
            best[i], dist[i] = 0, np.inf
            continue
        band = D[bo[i]:bo[i + 1]]
        costs = np.empty(len(correct))
        for j in range(len(correct)):
            costs[j] = bfs_distance(B[i], C[j], band[:, co[j]:co[j + 1]].astype(float)
                                    if C[j] else None)
        best[i] = int(costs.argmin())
        dist[i] = float(costs[best[i]])
    return best, dist


# --------------------------------------------------------------- clustering
@dataclass
class Cluster:
    label: int
    members: list[int]          # indices into the input list
    medoid: int                 # index of the most central member


def _medoid(indices: list[int], dist: np.ndarray) -> int:
    """Member minimizing summed distance to the rest of its cluster."""
    if len(indices) == 1:
        return indices[0]
    sub = dist[np.ix_(indices, indices)]
    return indices[int(sub.sum(axis=1).argmin())]


def _modal_member(members: list[int], docs: list[str], dist: np.ndarray) -> int:
    """The member whose repair the cluster most agrees on.

    Not the medoid, and not the member needing the smallest repair. The medoid is
    the most *typical program*, which in a large cluster is usually a multi-issue
    mess; the smallest repair is the one submission that came closest to correct,
    which is an outlier, not a spokesman. Blind audits kept turning up the same
    failure under both rules -- members agreeing with each other and disagreeing
    with the program chosen to speak for them -- so the representative is the
    member carrying the most common edit script, ties going to the smallest
    repair among those. When no script repeats, that degenerates to the medoid.
    """
    from collections import Counter
    sig = {i: " ".join(sorted(docs[i].split())) for i in members}
    counts = Counter(sig.values())
    best, n = counts.most_common(1)[0]
    if n > 1:
        share = [i for i in members if sig[i] == best]
        return min(share, key=lambda i: len(docs[i].split()))
    sub = dist[np.ix_(members, members)]
    return members[int(sub.sum(axis=1).argmin())]


def cluster_docs(docs: list[str], distance_threshold: float | None = 0.5
                 ) -> tuple[list[Cluster], np.ndarray]:
    """Cluster pre-tokenized documents by average linkage over cosine distance.

    ``distance_threshold=None`` selects the cut from the data instead: the tree
    is cut at whichever cluster count maximizes mean silhouette. A fixed height
    is not a smaller assumption than a fixed ``k`` -- it is the same choice in
    different clothes -- and 0.5 was never derived from anything. Sweeping it
    shows no knee, and the same constant produces six-fold different granularity
    across our assignments, so it does not transfer even between problems we
    already have.
    """
    n = len(docs)
    if n == 0:
        return [], np.zeros((0, 0))
    vec = TfidfVectorizer(token_pattern=r"[^\s]+", min_df=1, lowercase=False)
    if not any(docs):
        return [Cluster(0, list(range(n)), 0)], np.zeros((n, n))
    X = vec.fit_transform(docs)
    X = X.toarray() if hasattr(X, "toarray") else X
    if n == 1:
        return [Cluster(0, [0], 0)], np.zeros((1, 1))
    dist = np.clip(pairwise_distances(X, metric="cosine"), 0, None)
    np.fill_diagonal(dist, 0.0)
    labels = (_silhouette_cut(dist) if distance_threshold is None
              else AgglomerativeClustering(
                  n_clusters=None, distance_threshold=distance_threshold,
                  metric="precomputed", linkage="average").fit_predict(dist))
    clusters = [Cluster(int(l), [i for i in range(n) if labels[i] == l],
                        _modal_member([i for i in range(n) if labels[i] == l],
                                      docs, dist))
                for l in sorted(set(labels))]
    clusters.sort(key=lambda c: -len(c.members))
    return clusters, dist


def _silhouette_cut(dist: np.ndarray) -> np.ndarray:
    """Cut the average-linkage tree at the k with the best mean silhouette."""
    from scipy.cluster.hierarchy import fcluster, linkage
    from scipy.spatial.distance import squareform
    from sklearn.metrics import silhouette_score

    n = len(dist)
    if n < 4:
        return np.arange(n)
    Z = linkage(squareform(dist, checks=False), method="average")
    grid = sorted({int(round(v)) for v in np.linspace(2, n - 1, min(150, n - 2))})
    best, best_lab = -2.0, None
    for k in grid:
        lab = fcluster(Z, k, criterion="maxclust")
        if len(set(lab.tolist())) < 2:
            continue
        s = float(silhouette_score(dist, lab, metric="precomputed"))
        if s > best:
            best, best_lab = s, lab
    return best_lab if best_lab is not None else np.arange(n)


def cluster(sources: list[str], max_clusters: int | None = None) -> tuple[list[Cluster], np.ndarray]:
    """Cluster programs by structure; return clusters (with medoids) and the
    pairwise cosine-distance matrix used, so callers can reuse it.

    Cluster count is chosen from the data: we merge with average-linkage
    agglomerative clustering under a cosine-distance threshold, which needs no
    ``k``. ``max_clusters`` optionally caps the count (largest clusters kept).
    """
    n = len(sources)
    if n == 0:
        return [], np.zeros((0, 0))
    matrix, vec = structural_features(sources)
    X = matrix.toarray() if hasattr(matrix, "toarray") else matrix
    if n == 1 or vec is None:
        return [Cluster(0, list(range(n)), 0)], np.zeros((n, n))
    dist = pairwise_distances(X, metric="cosine")
    # distance_threshold=0 would put every unique shape in its own cluster;
    # 0.5 cosine merges programs sharing most of their AST-path vocabulary.
    model = AgglomerativeClustering(
        n_clusters=None, distance_threshold=0.5,
        metric="precomputed", linkage="average")
    labels = model.fit_predict(dist)

    clusters: list[Cluster] = []
    for lab in sorted(set(labels)):
        members = [i for i in range(n) if labels[i] == lab]
        clusters.append(Cluster(int(lab), members, _medoid(members, dist)))
    clusters.sort(key=lambda c: -len(c.members))
    if max_clusters is not None:
        clusters = clusters[:max_clusters]
    return clusters, dist


# --------------------------------------------------------------- reference pick
def nearest_reference(buggy: str, reference_pool: list[str]) -> str | None:
    """The correct solution this program is closest to *repairing into*.

    The same pairing the build step uses: sequences matched one-to-one across
    top-level definitions and aligned, so the partner is the one needing the
    fewest edit operations. What the fallback prompt wants to show the model is
    "what this student was reaching for", and the minimum-edit correct program
    is that by construction.

    The previous rule clustered the correct pool on AST shape, took the cluster
    nearest the buggy program, and returned a *random* member of it. That is
    three choices with no support: a hand-set merge threshold, shape as the
    axis, and an arbitrary pick within the winning cluster. None survives here.
    """
    pool = [r for r in reference_pool if r.strip()]
    if not pool:
        return None
    if len(pool) == 1:
        return pool[0]
    best, _dist = pair_by_bfs([buggy], pool)
    return pool[int(best[0])]
