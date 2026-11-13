n = input("")
answer = "NO"
x = 0
for num in n:
    if num == "4" or num == "7":
        answer = "YES"
    else:
        answer = "NO"
        break
print(answer)