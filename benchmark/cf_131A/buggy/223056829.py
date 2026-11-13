def judge(n):
    if n.upper()==n or n.capitalize()==n:
        return n
    else:
        return n.capitalize()

word=input()
print(judge(word))