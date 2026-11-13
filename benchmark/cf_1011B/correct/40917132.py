from collections import Counter


def solve(participants_count, packages):
    day = 1
    while sum(value//day for value in packages.values()) >= participants_count:
        day += 1

    return day-1


if __name__ == '__main__':
    participants, _ = map(int, input().split())
    packages = Counter(input().split())
    print(solve(participants, packages))