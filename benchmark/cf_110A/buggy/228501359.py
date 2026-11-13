# s_num = input()
#

def is_lucky(s_num):
    s_num = str(s_num)
    return not bool(s_num.replace('7', '').replace('4', ''))


# print('YES' if is_lucky(s_num) or is_lucky(str(len(s_num)))  else 'NO')
text = input()
if  is_lucky(str(len(text))):
    print('YES')
else:
    print('NO')