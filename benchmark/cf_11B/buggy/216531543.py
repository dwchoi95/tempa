class Solve:

    def __init__(self):
        self.x = 0;
        self.dem = 0;

    def vao(self):
        self.x = int(input());
    
    def lam(self):
        tong = 0;
        i = 1;
        while(tong + i<= abs(self.x)):
            tong += i;
            self.dem += 1;
            i += 1;
        if(tong < abs(self.x)):
            hieu = abs(self.x) - tong;
            self.dem += hieu * 2;
    
    def ra(self):
        print(self.dem);


def main():
    p = Solve();
    p.vao();
    p.lam();
    p.ra();

main();