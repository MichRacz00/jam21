#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <genmc.h>

atomic_int x;
atomic_int y;

void *thread_1(void *unused)
{
	atomic_store_explicit(&x, 1, memory_order_relaxed);
    atomic_store_explicit(&y, 1, memory_order_relaxed);
	
	return NULL;
}

void *thread_2(void *unused)
{
	atomic_store_explicit(&x, 2, memory_order_relaxed);
    atomic_thread_fence(memory_order_seq_cst);
    atomic_store_explicit(&y, 2, memory_order_relaxed);

	return NULL;
}

int main()
{
	pthread_t t1, t2;

	// To break [init] as sc access
	atomic_store_explicit(&x, 0, memory_order_relaxed);
	atomic_store_explicit(&y, 0, memory_order_relaxed);

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();

    pthread_join(t2, NULL);

    atomic_store_explicit(&x, 0, memory_order_relaxed);
    atomic_store_explicit(&y, 0, memory_order_relaxed);
	
	return 0;
}
