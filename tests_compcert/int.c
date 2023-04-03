#include <stdlib.h>

int f()
{
	return 3;
}

int main() {
	int x = 5+5;
	int y = 2+3;
	int * p = malloc(1);
	p = malloc(sizeof(int));

	int z = f();
	float fz = z;
	float fz2 = (float) z;

	double tableau[2];
	tableau[1] = 2.3;
	double* truc = &(tableau[1]);
	int *vtruc = *(&(truc));

	int i = 5;
	while (i > 1) {
		i++;
	}
	return 0;
}
