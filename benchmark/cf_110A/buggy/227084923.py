result = "hello world!"
n = int(input())
if 1 <= n and n <= 10**18:
    luckyNumbers = "47"
    lucky = False
    count = 0
    for s in str(n):
        if s in luckyNumbers:
            count += 1
    if count == len(str(n)):
        lucky = True
    if str(count) in luckyNumbers:
        result = "YES"
    elif lucky == False:
        result = "NO"
print(f"{result}")