class Solution:
	def __init__(self):
		pass

	def solve(self):
		s = input()

		if (s[0].islower() and s[1:].isupper()) or (s.isupper()):
			s = s.swapcase()

		print(s)

if __name__ == "__main__":
	sol = Solution()
	sol.solve()