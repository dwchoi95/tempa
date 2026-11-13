n=input()
test_str = n



res = ' '.join([word.capitalize() for word in test_str.split()])


print(str(res))