#!/usr/bin/env python
# coding: utf-8

# In[12]:


n=int(input())%1000000007
flag=False
for i in str(n):
    if i==str(4) or i==str(7):
        flag=True
    else:
        flag=False
if flag==True:
    print("YES")
else:
    print("NO")
        

    
    


# In[ ]: