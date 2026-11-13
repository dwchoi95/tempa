def judge(n):
    if n.upper()==n:
        return n.capitalize()
    elif n[0].lower()==n[0] and n[1:len(n)].upper()==n[1:len(n)]:
        return n.capitalize()
    else:
        return n

word=input()
print(judge(word))