#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <genmc.h>

atomic_int n;
atomic_int i;

void *thread_1(void *unused)
{
	atomic_thread_fence(memory_order_release);
	int n_local = atomic_load_explicit(&n, memory_order_release);
	atomic_store_explicit(&i, n_local, memory_order_seq_cst);
	atomic_thread_fence(memory_order_seq_cst);
	return NULL;
}

void *thread_2(void *unused)
{
	atomic_thread_fence(memory_order_release);
	int n_local = atomic_load_explicit(&n, memory_order_release);
	atomic_store_explicit(&i, n_local, memory_order_release);
	atomic_thread_fence(memory_order_seq_cst);
	return NULL;
}

atomic_int x;
atomic_int y;

pthread_barrier_t barrier;

void *thread_a(void *unused)
{
	pthread_barrier_wait(&barrier);
	pthread_barrier_destroy(&barrier);

	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_store_explicit(&y, 1, memory_order_release);
	return NULL;
}

void *thread_b(void *unused)
{
	if (atomic_load_explicit(&y, memory_order_acquire))
		if (atomic_load_explicit(&x, memory_order_relaxed))
			pthread_barrier_wait(&barrier);
	return NULL;
}


int main()
{
	pthread_t t1, t2;

	pthread_barrier_init(&barrier, NULL, 1);

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();

	pthread_t ta, tb;

	if (pthread_create(&ta, NULL, thread_a, NULL))
		abort();
	if (pthread_create(&tb, NULL, thread_b, NULL))
		abort();

	
	return 0;
}
