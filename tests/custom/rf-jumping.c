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
	int x_local = atomic_load_explicit(&x, memory_order_relaxed);

	__VERIFIER_assume(x_local == 2);
	
	return NULL;
}

void *thread_2(void *unused)
{
	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_store_explicit(&x, 2, memory_order_relaxed);
	atomic_store_explicit(&x, 3, memory_order_relaxed);
	atomic_store_explicit(&x, 4, memory_order_relaxed);

	return NULL;
}

int main()
{
	pthread_t t1, t2, t3, t4;

	// To break [init] as sc access
	atomic_store_explicit(&x, 0, memory_order_relaxed);
	atomic_store_explicit(&y, 0, memory_order_relaxed);

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();
	
	return 0;
}
