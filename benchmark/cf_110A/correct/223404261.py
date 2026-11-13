"""
@auther:Abdallah_Gaber 
"""
n = input()
if '4' not in n and '7' not in n:
    print("NO")
    quit()
lst = list(n)
a = lst.count('4')
b = lst.count('7')
if a + b == 4 or a +b == 7:
    print("YES")
else:
    print("NO")