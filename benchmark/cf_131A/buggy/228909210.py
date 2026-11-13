ss="aeiou"
s=input()
num=0
for i in range(0,len(s)):
    if s[i] in ss:
        num=i
print(s[0:num+1]+'ntry')