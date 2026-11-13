number = str(input())

num_4 = number.count("4")
num_7 = number.count("7")

num_t = num_4 + num_7
num_t_list = list(str(num_t))
print (num_t_list)
print (num_t)

if "1" in num_t_list or "2" in num_t_list or "3" in num_t_list or "5" in num_t_list or "6" in num_t_list or "8" in num_t_list or "9" in num_t_list or "0" in num_t_list:
    print ("NO")
else:
    print ("YES")