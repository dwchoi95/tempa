word = input()
idx = 0
new = ""
for i in word:
    
    j = str(i)
    if j != " ":
        j = j.lower()
        if idx == 0:
            j = j.capitalize()
    new += j
    idx += 1
print(new)