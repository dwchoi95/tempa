petya_input = input()
count = 0
for i in range(len(petya_input)):
    if petya_input[i] == "4" or petya_input[i] == "7":
        count += 1
if count == 4 or count == 7:
    print("YES")
else:
    print("NO")