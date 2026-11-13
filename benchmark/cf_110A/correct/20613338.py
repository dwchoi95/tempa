S = input()
cnt_four = S.count("4")
cnt_seven = S.count("7")
cnt = cnt_four + cnt_seven
cnt_str = str(cnt)
for s in cnt_str:
    if s != "4" and s != "7":
        print("NO")
        exit()
print("YES")