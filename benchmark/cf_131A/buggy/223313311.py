a=str(input())
dont=False
for k in range(len(a)):
    if a[k] != a[k].upper() and k>=1:
        dont=True
        break
if len(a)==1:
        print(a.lower())
else:
    if not dont:
        print(a[0].upper()+a[1:].lower())