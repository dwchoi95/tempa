n=str(int(input()))
for i in range (len(n)):
 if (n[i]==4 or n[i]==7) and (len(n)==7 or len(n)==4):
      print("YES")
      break
 else:
      print("NO")    
      break