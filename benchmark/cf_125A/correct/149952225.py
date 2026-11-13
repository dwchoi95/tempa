from itertools import permutations

# Test_case = int(input())
Test_case = 1


for test in range(Test_case):
    n = int(input())
    if n % 3 == 0:
        inc = n // 3
        print(inc // 12, inc % 12)
    elif n % 3 == 1:
        inc = n // 3
        print(inc // 12, inc % 12)
    else:
        inc = n // 3 + 1
        print(inc // 12, inc % 12)
    # a = []
    # n, m = map(int, input().split())
    # for i in range(n):
    #     temp = []
    #     s = input()
    #     for j in range(m):
    #         temp.append(s[j])
    #     a.append(temp)
    # cnt = 0
    # for ii in range(n):
    #     for jj in range(m):
    #         if a[ii][jj] == 'W':
    #             if ii
    #
    #             # if a[max(ii - 1, 0)][max(jj - 1, 0)] == 'P':
    #             #     a[max(ii - 1, 0)][max(jj - 1, 0)] = '1'
    #             #     cnt += 1
    #             # elif a[min(ii + 1, n - 1)][min(jj + 1 , n - 1)] == 'P':
    #             #     cnt += 1
    #             #     a[min(ii + 1, n - 1)][min(jj + 1, n - 1)] = '1'
    #             # elif a[ii][min(jj + 1, m - 1)] == 'P':
    #             #     cnt += 1
    #             #     a[ii][min(jj + 1, m - 1)] = '1'
    #             # elif a[ii][max(jj - 1, 0)] == 'P':
    #             #     cnt += 1
    #             #     a[ii][max(jj - 1, 0)] = '1'
    # print(cnt)