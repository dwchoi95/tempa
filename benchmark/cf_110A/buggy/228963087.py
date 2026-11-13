#!/usr/bin/env python
# coding: utf-8

# In[23]:


n=int(input())%1000000007
element={"4","7"}
for i in str(n):
    if i==str(4)and i==str(7):
        flag=True
    else:
        flag=False
if flag==True:
    print("YES")
else:
    print("NO")
        

    
    


# In[ ]: