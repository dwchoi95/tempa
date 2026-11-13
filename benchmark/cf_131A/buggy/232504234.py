s = input()
count = 0
new_str = ""
if 1<=len(s)<=100:
    if 97<=ord(s[0])<=122:
        for i in range(1, len(s)):
            if 65<=ord(s[i])<=90:
                count += 1
        if count == len(s)-1:
            new_str += chr(ord(s[0])-32)
            for m in range(1, len(s)):
                new_str += chr(ord(s[m])+32)
        else:
            new_str = s
    elif 65<=ord(s[0])<=90:
        for j in range(1, len(s)):
            if 65<=ord(s[j])<=90:
                count += 1
        if count == len(s)-1:
            new_str += s[0]
            for n in range(1, len(s)):
                new_str += chr(ord(s[n])+32)
        else:
            new_str = s
print(new_str)