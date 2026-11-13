n = input("")
answer = "NO"
x = 0
for num in n:
    if num == "4" or num == "7":
        x += 1
        if x == 4 or x == 7: 
            answer = "YES" 
        else:
            answer = "NO"
print(answer)