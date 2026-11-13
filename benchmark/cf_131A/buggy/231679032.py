s=input()
s1=s
new_word=''
if s==s.title():
    print(s)
else:
    for i in s:
        if (ord(i)>94)and(ord(i)<122):
            new_word+=i.upper()
        else:
            new_word+=i.lower()
    print(new_word)