number_test_list=list(input())#int不能被list化
num_lucky=0
for i in range(len(number_test_list)):
    if number_test_list[i] in ["4","7"]:
        num_lucky+=1

test=True
lucky_list=list(str(num_lucky))#因为int不能被list化
for j in range(len(lucky_list)):
    if lucky_list[j] not in ["4","7"]:
        test=False

if test:
    print("YES")
else:
    print("NO")