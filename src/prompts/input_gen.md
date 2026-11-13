You are writing a random test-input generator for a programming assignment.

## Problem
{description}

## The instructor's test suite (JSON, one test per line)
{tests}

## The instructor's reference solution
```python
{reference}
```
{feedback}
## Task
Write a Python function `gen(rng)` that takes a `random.Random` instance and returns ONE random test input: a dict in exactly the format of the tests above, without the "expected" field.
Rules:
- Every input must be valid under the assignment's specification and the reference's assumptions (argument types, value ranges, preconditions such as sortedness or distinctness). Never generate an input the reference would reject.
- If the suite uses "entry", choose it at random among the functions the suite calls, and generate arguments that fit the chosen function.
- Keep inputs small (about ten elements at most) and draw values from narrow ranges, so that duplicates, ties, and collisions occur often.
- Generate edge cases with non-trivial probability: empty and single-element collections, boundary values, and values both present in and absent from a collection.
- Use only `rng` for randomness and only the standard library.
- Do not add comments or explanations.
- Output ONLY the function in a single ```python code block.
