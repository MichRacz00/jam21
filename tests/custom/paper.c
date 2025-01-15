#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <genmc.h>

atomic_int x;
atomic_int y;

void __VERIFIER_assume(int);

void *thread_1(void *unused)
{
	atomic_store_explicit(&x, 2, memory_order_seq_cst);
	__VERIFIER_assume(y == 0);
	return NULL;
}

void *thread_2(void *unused)
{
	atomic_store_explicit(&y, 1, memory_order_seq_cst);
	return NULL;
}

void *thread_3(void *unused)
{
	__VERIFIER_assume(y == 1);
	atomic_store_explicit(&x, 1, memory_order_seq_cst);
	return NULL;
}

void *thread_4(void *unused)
{
	__VERIFIER_assume(x == 1);
	__VERIFIER_assume(x == 2);
	return NULL;
}


int main()
{
	pthread_t t1, t2, t3, t4;

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();
	if (pthread_create(&t3, NULL, thread_3, NULL))
		abort();
	if (pthread_create(&t4, NULL, thread_4, NULL))
		abort();
	
	return 0;
}
