s=input()
a,b=s.count('4'),s.count('7')
print("YES" if a==7 or a==4 or b==7 or b==4 or (a+b)==len(s) else "NO")