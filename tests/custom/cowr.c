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
	atomic_store_explicit(&x, 1, memory_order_seq_cst);
	atomic_load_explicit(&y, memory_order_seq_cst);
	
	return NULL;
}

void *thread_2(void *unused)
{
	return NULL;
}


int main()
{
	pthread_t t1, t2, t3, t4;

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();
	
	return 0;
}
