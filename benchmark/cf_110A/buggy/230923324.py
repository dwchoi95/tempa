import sys


def inp():
    return int(input())


def inlt():
    return list(map(int, input().split()))


def int_to_arr():
    return list(map(int, str(input()).strip()))


def insr():
    return input().strip()


def out(x):
    sys.stdout.write(str(x) + "\n")


# def is_upper(a):
#     return ord(a) >= 65 and ord(a) <= 90


# def is_lower(a):
#     return ord(a) >= 97 and ord(a) <= 122


# def to_upper(a):
#     ans = ""
#     for i in a:
#         if ord(i) >= 97 and ord(i) <= 122:
#             ans = ans + chr(ord(i) - 32)
#         else:
#             ans = ans + i
#     return ans


# def to_lower(a):
#     ans = ""
#     for i in a:
#         if ord(i) >= 65 and ord(i) <= 90:
#             ans = ans + chr(ord(i) + 32)
#         else:
#             ans = ans + i
#     return ans


def main():
    input_string = int_to_arr()
    count = 0

    for i in input_string:
        if i in [4, 7]:
            count += 1
    out("YES" if count >= 4 and count <= 7 else "NO")


if __name__ == "__main__":
    main()