class Solution:
	def __init__(self):
		pass

	def solve(self):
		s = input()
		string = ""

		if (s[0].islower() and s[1:].isupper()) or (s.isupper()):
			string += s[0].upper() + s[1:].lower()
		else:
			string = s

		print(string)

if __name__ == "__main__":
	sol = Solution()
	sol.solve()