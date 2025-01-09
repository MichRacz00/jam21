#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <genmc.h>

atomic_int x;
atomic_int y;

atomic_int n;

pthread_barrier_t barrier;

void *thread_1(void *unused)
{
	pthread_barrier_wait(&barrier);
	pthread_barrier_destroy(&barrier);

	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_store_explicit(&y, 1, memory_order_release);
	return NULL;
}

void *thread_2(void *unused)
{
	if (atomic_load_explicit(&y, memory_order_acquire))
		if (atomic_load_explicit(&x, memory_order_relaxed))
			pthread_barrier_wait(&barrier);
	return NULL;
}

void *thread_3(void *unused)
{
    atomic_store_explicit(&n, 1, memory_order_relaxed);
	atomic_thread_fence(memory_order_seq_cst);
	atomic_store_explicit(&n, 2, memory_order_relaxed);
	
	atomic_thread_fence(memory_order_acquire);
	
	atomic_store_explicit(&n, 0, memory_order_relaxed);
	atomic_thread_fence(memory_order_seq_cst);
	atomic_store_explicit(&n, 42, memory_order_relaxed);
	return NULL;
}


int main()
{
	pthread_t t1, t2, t3;

	pthread_barrier_init(&barrier, NULL, 1);

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();
	if (pthread_create(&t3, NULL, thread_3, NULL))
		abort();

	return 0;
}
