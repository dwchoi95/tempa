def is_lucky(n):
    if n in [4,7]:
        return 'YES'
    elif n in [0,1,2,3,5,6,8,9]:
        return 'NO'
    else:
        if n % 10 not in [4,7]:
            return 'NO'
        else:
            return is_lucky(n // 10)


st = input()
print(is_lucky(st.count('4')+st.count('7')))