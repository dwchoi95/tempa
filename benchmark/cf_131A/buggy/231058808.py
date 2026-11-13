# LUOGU_RID: 133058732
'''
#include<bits/stdc++.h>//1
using namespace std;//xx
string a;
int main()//fayHVGDUS
{
    cin>>a;
    for(int i=0;i<a.size();i++){
        if(i==0&&a[i]>='a'&&a[i]<='z'){
            toupper(a[i]);
        }
        else{
            tolower(a[i]);
        }
    }
    cout<<a;
    return 0;
}
'''
a = input()
s = list(a)
for i in range(0,len(s)):
    if i == 0 and ord(s[i]) >= ord('a') and ord(s[i]) <= ord('z'):
        s[i] = chr(ord(a[i])-32)
    elif ord(s[i]) >= ord('A') and ord(s[i]) <= ord('Z'):
        s[i] = chr(ord(a[i])+32)
ans=str()
for i in range(0,len(s)):
    ans+=s[i]
print(ans)
#lxm