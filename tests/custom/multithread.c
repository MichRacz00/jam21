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
	atomic_store_explicit(&x, 11, memory_order_relaxed);
	atomic_store_explicit(&x, 12, memory_order_relaxed);
	
	return NULL;
}

void *thread_2(void *unused)
{
	atomic_store_explicit(&x, 22, memory_order_relaxed);
	atomic_store_explicit(&x, 23, memory_order_relaxed);
	atomic_store_explicit(&x, 24, memory_order_relaxed);
	atomic_store_explicit(&x, 25, memory_order_relaxed);

	return NULL;
}

void *thread_3(void *unused)
{
	atomic_store_explicit(&x, 31, memory_order_relaxed);
	atomic_store_explicit(&x, 32, memory_order_relaxed);

	return NULL;
}

void *thread_4(void *unused)
{
	atomic_store_explicit(&x, 41, memory_order_relaxed);
	atomic_store_explicit(&x, 42, memory_order_relaxed);

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
	if (pthread_create(&t3, NULL, thread_3, NULL))
		abort();
	if (pthread_create(&t4, NULL, thread_4, NULL))
		abort();
	
	return 0;
}
