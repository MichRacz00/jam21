#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>

#include "../peterZ.c"

int main()
{
	pthread_t t1, t2, t3;

	atomic_store_explicit(&x,0,memory_order_relaxed);
	atomic_store_explicit(&y,0,memory_order_relaxed);
	atomic_store_explicit(&z,0,memory_order_relaxed);

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();
	if (pthread_create(&t3, NULL, thread_3, NULL))
		abort();

	return 0;
}
