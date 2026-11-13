num = [*input()]
LuckyNumberCount = 0

for i in range(len(num)):
    if (num[i] == "7") or (num[i] == "4"):
        LuckyNumberCount += 1

LuckyNumberCount = str(LuckyNumberCount)
if len(LuckyNumberCount) - (LuckyNumberCount.count("4")+LuckyNumberCount.count("7")) == 0:
    print("YES")
else:
    print("NO")