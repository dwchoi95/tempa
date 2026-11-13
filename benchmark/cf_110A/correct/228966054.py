#!/usr/bin/env python
# coding: utf-8

# In[38]:


n = input()
count = 0
for digit in n:
    if digit == '4' or digit == '7':
        count += 1
if set(str(count)) <= set('47'):
    print("YES")
else:
    print("NO")


    
    


# 

# In[ ]: