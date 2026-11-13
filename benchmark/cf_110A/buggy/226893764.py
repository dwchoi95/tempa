#!/usr/bin/env python
# coding: utf-8

# In[20]:


num = input()
cnt = 0
for char in num:
    if char ==4 or 7:
        cnt+=1
if cnt == 4 or 7:
    print('YES')
else:
    print('NO')


# In[ ]: