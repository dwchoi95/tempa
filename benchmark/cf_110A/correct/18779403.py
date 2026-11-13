n=input()
nsn=n.count('4')+n.count('7')
nsnsn=str(nsn).count('4')+str(nsn).count('7')
if nsnsn==len(str(nsn)):
    print("YES")
else:
    print("NO")