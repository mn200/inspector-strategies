# 1 "expr.c"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 170 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "expr.c" 2


int main() {
  int x;
  int y = 6;
  x = 8;
  x = 1 + y;
  x = 2 - y;
  x = 3 * y;
  x = 4 / y;
  x = y++;
  x = (5 + y) * x;
  x = 6 + y * 7 - 23 / y;

  return 0;
}
