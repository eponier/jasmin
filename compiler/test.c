#include <stdio.h>

int foo (int x);

int main() {
  int x;
  x = foo (5);

  printf ("%d\n", x);

  return 0;
}
