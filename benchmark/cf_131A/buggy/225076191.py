def Standard(s):
    for i in range(1,len(s)):
        if s[i]!=s[i].upper():
            return s
    return s[0].upper()+s[1:len(s)].lower()


if __name__=="__main__":
    s=input()
    print(Standard(s))