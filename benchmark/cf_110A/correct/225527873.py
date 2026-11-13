n=input()
s=str(n.count("7")+n.count("4"))
print("YES" if len(s.replace('7','').replace('4',''))==0 else "NO")