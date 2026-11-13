import queue

class Solve:

    def __init__(self) -> None:
        self.x = 0;
        self.dem = 0;

    def vao(self) -> None:
        self.x = int(input());
    
    def lam(self) -> None:
        tong = 0;
        # Vòng while lặp đến khi tìm được số có hiệu của số đó với x chia hết cho 2
        # Biến tổng được tính bằng cách cộng các chỉ số của mỗi bước nhảy tiến cho đến khi thỏa mãn điều kiện
        # Vậy khi thay 1 bước nhảy bất kỳ thành lùi thì tổng sẽ giảm đi một lượng là 2 * chỉ số của bước nhảy tương ứng
        while(tong < self.dem or (tong - self.dem) % 2 != 0):
            self.dem += 1;
            tong += self.dem;
    
    def ra(self) -> None:
        print(self.dem);


def main():
    p = Solve();
    p.vao();
    p.lam();
    p.ra();

main();