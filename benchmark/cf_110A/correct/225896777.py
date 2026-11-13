n = str(input())
ans = 'NO'
counts = 0
for i in n:
	if i=='4' or i == '7':
		counts += 1		
if counts ==4 or counts==7:
	ans = 'YES'		
print(ans)