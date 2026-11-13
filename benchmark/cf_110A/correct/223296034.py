def nearly_lucky_number():
    n = input()
    i = n.count('4') + n.count('7')
    print('YES' if i == 4 or i == 7 else 'NO')
 
if __name__ == '__main__':
    nearly_lucky_number()