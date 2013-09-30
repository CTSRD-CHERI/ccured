/* 
 * Copyright (c) 1994 by Xerox Corporation.  All rights reserved.
 * Copyright (c) 1996 by Silicon Graphics.  All rights reserved.
 * Copyright (c) 1998 by Fergus Henderson.  All rights reserved.
 * Copyright (c) 2000-2001 by Hewlett-Packard Company.  All rights reserved.
 *
 * THIS MATERIAL IS PROVIDED AS IS, WITH ABSOLUTELY NO WARRANTY EXPRESSED
 * OR IMPLIED.  ANY USE IS AT YOUR OWN RISK.
 *
 * Permission is hereby granted to use or copy this program
 * for any purpose,  provided the above notices are retained on all copies.
 * Permission to modify the code and to distribute modified code is granted,
 * provided the above notices are retained, and a notice that the code was
 * modified is included with the above copyright notice.
 */
/*
 * Support code for LinuxThreads, the clone()-based kernel
 * thread package for Linux which is included in libc6.
 *
 * This code relies on implementation details of LinuxThreads,
 * (i.e. properties not guaranteed by the Pthread standard),
 * though this version now does less of that than the other Pthreads
 * support code.
 *
 * Note that there is a lot of code duplication between linux_threads.c
 * and thread support for some of the other Posix platforms; any changes
 * made here may need to be reflected there too.
 */
 /* DG/UX ix86 support <takis@xfree86.org> */
/*
 * Linux_threads.c now also includes some code to support HPUX and
 * OSF1 (Compaq Tru64 Unix, really).  The OSF1 support is not yet
 * functional.  The OSF1 code is based on Eric Benson's
 * patch, though that was originally against hpux_irix_threads.  The code
 * here is completely untested.  With 0.0000001% probability, it might
 * actually work.
 *
 * Eric also suggested an alternate basis for a lock implementation in
 * his code:
 * + #elif defined(OSF1)
 * +    unsigned long GC_allocate_lock = 0;
 * +    msemaphore GC_allocate_semaphore;
 * + #  define GC_TRY_LOCK() \
 * +    ((msem_lock(&GC_allocate_semaphore, MSEM_IF_NOWAIT) == 0) \
 * +     ? (GC_allocate_lock = 1) \
 * +     : 0)
 * + #  define GC_LOCK_TAKEN GC_allocate_lock
 */

/* #define DEBUG_THREADS 1 */

/* ANSI C requires that a compilation unit contains something */

# include "gc.h"

# if defined(GC_PTHREADS) && !defined(GC_SOLARIS_THREADS) \
     && !defined(GC_IRIX_THREADS) && !defined(GC_WIN32_THREADS)

# include "private/gc_priv.h"

# if defined(GC_HPUX_THREADS) && !defined(USE_PTHREAD_SPECIFIC) \
     && !defined(USE_HPUX_TLS)
#   define USE_HPUX_TLS
# endif

# if (defined(GC_DGUX386_THREADS) || defined(GC_OSF1_THREADS)) \
      && !defined(USE_PTHREAD_SPECIFIC)
#   define USE_PTHREAD_SPECIFIC
# endif

# if defined(GC_DGUX386_THREADS) && !defined(_POSIX4A_DRAFT10_SOURCE)
#   define _POSIX4A_DRAFT10_SOURCE 1
# endif

# if defined(GC_DGUX386_THREADS) && !defined(_USING_POSIX4A_DRAFT10)
#   define _USING_POSIX4A_DRAFT10 1
# endif

# ifdef THREAD_LOCAL_ALLOC
#   if !defined(USE_PTHREAD_SPECIFIC) && !defined(USE_HPUX_TLS)
#     include "private/specific.h"
#   endif
#   if defined(USE_PTHREAD_SPECIFIC)
#     define GC_getspecific pthread_getspecific
#     define GC_setspecific pthread_setspecific
#     define GC_key_create pthread_key_create
      typedef pthread_key_t GC_key_t;
#   endif
#   if defined(USE_HPUX_TLS)
#     define GC_getspecific(x) (x)
#     define GC_setspecific(key, v) ((key) = (v), 0)
#     define GC_key_create(key, d) 0
      typedef void * GC_key_t;
#   endif
# endif
# include <stdlib.h>
# include <pthread.h>
# include <sched.h>
# include <time.h>
# include <errno.h>
# include <unistd.h>
# include <sys/mman.h>
# include <sys/time.h>
# include <semaphore.h>
# include <signal.h>
# include <sys/types.h>
# include <sys/stat.h>
# include <fcntl.h>

#if defined(GC_DGUX386_THREADS)
# include <sys/dg_sys_info.h>
# include <sys/_int_psem.h>
  /* sem_t is an uint in DG/UX */
  typedef unsigned int  sem_t;
#endif /* GC_DGUX386_THREADS */

#ifndef __GNUC__
#   define __inline__
#endif

#ifdef GC_USE_LD_WRAP
#   define WRAP_FUNC(f) __wrap_##f
#   define REAL_FUNC(f) __real_##f
#else
#   define WRAP_FUNC(f) GC_##f
#   if !defined(GC_DGUX386_THREADS)
#     define REAL_FUNC(f) f
#   else /* GC_DGUX386_THREADS */
#     define REAL_FUNC(f) __d10_##f
#   endif /* GC_DGUX386_THREADS */
#   undef pthread_create
#   undef pthread_sigmask
#   undef pthread_join
#   undef pthread_detach
#endif


void GC_thr_init();

#if DEBUG_THREADS

#ifndef NSIG
# if defined(MAXSIG)
#  define NSIG (MAXSIG+1)
# elif defined(_NSIG)
#  define NSIG _NSIG
# elif defined(__SIGRTMAX)
#  define NSIG (__SIGRTMAX+1)
# else
  --> please fix it
# endif
#endif

void GC_print_sig_mask()
{
    sigset_t blocked;
    int i;

    if (pthread_sigmask(SIG_BLOCK, NULL, &blocked) != 0)
    	ABORT("pthread_sigmask");
    GC_printf0("Blocked: ");
    for (i = 1; i < NSIG; i++) {
        if (sigismember(&blocked, i)) { GC_printf1("%ld ",(long) i); }
    }
    GC_printf0("\n");
}
#endif

word GC_stop_count;	/* Incremented at the beginning of GC_stop_world. */

#ifdef GC_OSF1_THREADS
  GC_bool GC_retry_signals = TRUE;
#else
  GC_bool GC_retry_signals = FALSE;
#endif

/* We use the allocation lock to protect thread-related data structures. */

/* The set of all known threads.  We intercept thread creation and 	*/
/* joins.								*/
/* Protected by allocation/GC lock.					*/
/* Some of this should be declared volatile, but that's inconsistent	*/
/* with some library routine declarations.  		 		*/
typedef struct GC_Thread_Rep {
    struct GC_Thread_Rep * next;  /* More recently allocated threads	*/
				  /* with a given pthread id come 	*/
				  /* first.  (All but the first are	*/
				  /* guaranteed to be dead, but we may  */
				  /* not yet have registered the join.) */
    pthread_t id;
    short flags;
#	define FINISHED 1   	/* Thread has exited.	*/
#	define DETACHED 2	/* Thread is intended to be detached.	*/
#	define MAIN_THREAD 4	/* True for the original thread only.	*/
    short thread_blocked;	/* Protected by GC lock.		*/
    				/* Treated as a boolean value.  If set,	*/
    				/* thread will acquire GC lock before	*/
    				/* doing any pointer manipulations, and	*/
    				/* has set its sp value.  Thus it does	*/
    				/* not need to be sent a signal to stop	*/
    				/* it.					*/
    ptr_t stack_end;		/* Cold end of the stack.		*/
    ptr_t stack_ptr;  		/* Valid only when stopped.      	*/
#   ifdef IA64
	ptr_t backing_store_end;
	ptr_t backing_store_ptr;
#   endif
    int	signal;
    void * status;		/* The value returned from the thread.  */
    				/* Used only to avoid premature 	*/
				/* reclamation of any data it might 	*/
				/* reference.				*/
    word last_stop_count;	/* GC_last_stop_count value when thread	*/
    				/* last successfully handled a suspend	*/
    				/* signal.				*/
#   ifdef THREAD_LOCAL_ALLOC
#	if CPP_WORDSZ == 64 && defined(ALIGN_DOUBLE)
#	    define GRANULARITY 16
#	    define NFREELISTS 49
#	else
#	    define GRANULARITY 8
#	    define NFREELISTS 65
#	endif
	/* The ith free list corresponds to size i*GRANULARITY */
#	define INDEX_FROM_BYTES(n) ((ADD_SLOP(n) + GRANULARITY - 1)/GRANULARITY)
#	define BYTES_FROM_INDEX(i) ((i) * GRANULARITY - EXTRA_BYTES)
#	define SMALL_ENOUGH(bytes) (ADD_SLOP(bytes) <= \
				    (NFREELISTS-1)*GRANULARITY)
	ptr_t ptrfree_freelists[NFREELISTS];
	ptr_t normal_freelists[NFREELISTS];
#	ifdef GC_GCJ_SUPPORT
	  ptr_t gcj_freelists[NFREELISTS];
#	endif
		/* Free lists contain either a pointer or a small count */
		/* reflecting the number of granules allocated at that	*/
		/* size.						*/
		/* 0 ==> thread-local allocation in use, free list	*/
		/*       empty.						*/
		/* > 0, <= DIRECT_GRANULES ==> Using global allocation,	*/
		/*       too few objects of this size have been		*/
		/* 	 allocated by this thread.			*/
		/* >= HBLKSIZE  => pointer to nonempty free list.	*/
		/* > DIRECT_GRANULES, < HBLKSIZE ==> transition to	*/
		/*    local alloc, equivalent to 0.			*/
#	define DIRECT_GRANULES (HBLKSIZE/GRANULARITY)
		/* Don't use local free lists for up to this much 	*/
		/* allocation.						*/
#   endif
} * GC_thread;

GC_thread GC_lookup_thread(pthread_t id);

static GC_bool parallel_initialized = FALSE;

void GC_init_parallel();

# if defined(THREAD_LOCAL_ALLOC) && !defined(DBG_HDRS_ALL)

/* We don't really support thread-local allocation with DBG_HDRS_ALL */

#ifdef USE_HPUX_TLS
  __thread
#endif
GC_key_t GC_thread_key;

static GC_bool keys_initialized;

/* Recover the contents of the freelist array fl into the global one gfl.*/
/* Note that the indexing scheme differs, in that gfl has finer size	*/
/* resolution, even if not all entries are used.			*/
/* We hold the allocator lock.						*/
static void return_freelists(ptr_t *fl, ptr_t *gfl)
{
    int i;
    ptr_t q, *qptr;
    size_t nwords;

    for (i = 1; i < NFREELISTS; ++i) {
	nwords = i * (GRANULARITY/sizeof(word));
        qptr = fl + i;	
	q = *qptr;
	if ((word)q >= HBLKSIZE) {
	  if (gfl[nwords] == 0) {
	    gfl[nwords] = q;
	  } else {
	    /* Concatenate: */
	    for (; (word)q >= HBLKSIZE; qptr = &(obj_link(q)), q = *qptr);
	    GC_ASSERT(0 == q);
	    *qptr = gfl[nwords];
	    gfl[nwords] = fl[i];
	  }
	}
	/* Clear fl[i], since the thread structure may hang around.	*/
	/* Do it in a way that is likely to trap if we access it.	*/
	fl[i] = (ptr_t)HBLKSIZE;
    }
}

/* We statically allocate a single "size 0" object. It is linked to	*/
/* itself, and is thus repeatedly reused for all size 0 allocation	*/
/* requests.  (Size 0 gcj allocation requests are incorrect, and	*/
/* we arrange for those to fault asap.)					*/
static ptr_t size_zero_object = (ptr_t)(&size_zero_object);

/* Each thread structure must be initialized.	*/
/* This call must be made from the new thread.	*/
/* Caller holds allocation lock.		*/
void GC_init_thread_local(GC_thread p)
{
    int i;

    if (!keys_initialized) {
	if (0 != GC_key_create(&GC_thread_key, 0)) {
	    ABORT("Failed to create key for local allocator");
        }
	keys_initialized = TRUE;
    }
    if (0 != GC_setspecific(GC_thread_key, p)) {
	ABORT("Failed to set thread specific allocation pointers");
    }
    for (i = 1; i < NFREELISTS; ++i) {
	p -> ptrfree_freelists[i] = (ptr_t)1;
	p -> normal_freelists[i] = (ptr_t)1;
#	ifdef GC_GCJ_SUPPORT
	  p -> gcj_freelists[i] = (ptr_t)1;
#	endif
    }   
    /* Set up the size 0 free lists.	*/
    p -> ptrfree_freelists[0] = (ptr_t)(&size_zero_object);
    p -> normal_freelists[0] = (ptr_t)(&size_zero_object);
#   ifdef GC_GCJ_SUPPORT
        p -> gcj_freelists[0] = (ptr_t)(-1);
#   endif
}

#ifdef GC_GCJ_SUPPORT
  extern ptr_t * GC_gcjobjfreelist;
#endif

/* We hold the allocator lock.	*/
void GC_destroy_thread_local(GC_thread p)
{
    /* We currently only do this from the thread itself or from	*/
    /* the fork handler for a child process.			*/
#   ifndef HANDLE_FORK
      GC_ASSERT(GC_getspecific(GC_thread_key) == (void *)p);
#   endif
    return_freelists(p -> ptrfree_freelists, GC_aobjfreelist);
    return_freelists(p -> normal_freelists, GC_objfreelist);
#   ifdef GC_GCJ_SUPPORT
   	return_freelists(p -> gcj_freelists, GC_gcjobjfreelist);
#   endif
}

extern GC_PTR GC_generic_malloc_many();

GC_PTR GC_local_malloc(size_t bytes)
{
    if (EXPECT(!SMALL_ENOUGH(bytes),0)) {
        return(GC_malloc(bytes));
    } else {
	int index = INDEX_FROM_BYTES(bytes);
	ptr_t * my_fl;
	ptr_t my_entry;
	GC_key_t k = GC_thread_key;
	void * tsd;

#	if defined(REDIRECT_MALLOC) && !defined(USE_PTHREAD_SPECIFIC)
	    if (EXPECT(0 == k, 0)) {
		/* This can happen if we get called when the world is	*/
		/* being initialized.  Whether we can actually complete	*/
		/* the initialization then is unclear.			*/
		GC_init_parallel();
		k = GC_thread_key;
	    }
#	endif
	tsd = GC_getspecific(GC_thread_key);
#	ifdef GC_ASSERTIONS
	  LOCK();
	  GC_ASSERT(tsd == (void *)GC_lookup_thread(pthread_self()));
	  UNLOCK();
#	endif
	my_fl = ((GC_thread)tsd) -> normal_freelists + index;
	my_entry = *my_fl;
	if (EXPECT((word)my_entry >= HBLKSIZE, 1)) {
	    ptr_t next = obj_link(my_entry);
	    GC_PTR result = (GC_PTR)my_entry;
	    *my_fl = next;
	    obj_link(my_entry) = 0;
	    PREFETCH_FOR_WRITE(next);
	    return result;
	} else if ((word)my_entry - 1 < DIRECT_GRANULES) {
	    *my_fl = my_entry + index + 1;
            return GC_malloc(bytes);
	} else {
	    GC_generic_malloc_many(BYTES_FROM_INDEX(index), NORMAL, my_fl);
	    if (*my_fl == 0) return GC_oom_fn(bytes);
	    return GC_local_malloc(bytes);
	}
    }
}

GC_PTR GC_local_malloc_atomic(size_t bytes)
{
    if (EXPECT(!SMALL_ENOUGH(bytes), 0)) {
        return(GC_malloc_atomic(bytes));
    } else {
	int index = INDEX_FROM_BYTES(bytes);
	ptr_t * my_fl = ((GC_thread)GC_getspecific(GC_thread_key))
		        -> ptrfree_freelists + index;
	ptr_t my_entry = *my_fl;
	if (EXPECT((word)my_entry >= HBLKSIZE, 1)) {
	    GC_PTR result = (GC_PTR)my_entry;
	    *my_fl = obj_link(my_entry);
	    return result;
	} else if ((word)my_entry - 1 < DIRECT_GRANULES) {
	    *my_fl = my_entry + index + 1;
            return GC_malloc_atomic(bytes);
	} else {
	    GC_generic_malloc_many(BYTES_FROM_INDEX(index), PTRFREE, my_fl);
	    /* *my_fl is updated while the collector is excluded;	*/
	    /* the free list is always visible to the collector as 	*/
	    /* such.							*/
	    if (*my_fl == 0) return GC_oom_fn(bytes);
	    return GC_local_malloc_atomic(bytes);
	}
    }
}

#ifdef GC_GCJ_SUPPORT

#include "include/gc_gcj.h"

#ifdef GC_ASSERTIONS
  extern GC_bool GC_gcj_malloc_initialized;
#endif

extern int GC_gcj_kind;

GC_PTR GC_local_gcj_malloc(size_t bytes,
			   void * ptr_to_struct_containing_descr)
{
    GC_ASSERT(GC_gcj_malloc_initialized);
    if (EXPECT(!SMALL_ENOUGH(bytes), 0)) {
        return GC_gcj_malloc(bytes, ptr_to_struct_containing_descr);
    } else {
	int index = INDEX_FROM_BYTES(bytes);
	ptr_t * my_fl = ((GC_thread)GC_getspecific(GC_thread_key))
	                -> gcj_freelists + index;
	ptr_t my_entry = *my_fl;
	if (EXPECT((word)my_entry >= HBLKSIZE, 1)) {
	    GC_PTR result = (GC_PTR)my_entry;
	    GC_ASSERT(!GC_incremental);
	    /* We assert that any concurrent marker will stop us.	*/
	    /* Thus it is impossible for a mark procedure to see the 	*/
	    /* allocation of the next object, but to see this object 	*/
	    /* still containing a free list pointer.  Otherwise the 	*/
	    /* marker might find a random "mark descriptor".		*/
	    *(volatile ptr_t *)my_fl = obj_link(my_entry);
	    /* We must update the freelist before we store the pointer.	*/
	    /* Otherwise a GC at this point would see a corrupted	*/
	    /* free list.						*/
	    /* A memory barrier is probably never needed, since the 	*/
	    /* action of stopping this thread will cause prior writes	*/
	    /* to complete.						*/
	    GC_ASSERT(((void * volatile *)result)[1] == 0); 
	    *(void * volatile *)result = ptr_to_struct_containing_descr; 
	    return result;
	} else if ((word)my_entry - 1 < DIRECT_GRANULES) {
	    if (!GC_incremental) *my_fl = my_entry + index + 1;
	    	/* In the incremental case, we always have to take this */
	    	/* path.  Thus we leave the counter alone.		*/
            return GC_gcj_malloc(bytes, ptr_to_struct_containing_descr);
	} else {
	    GC_generic_malloc_many(BYTES_FROM_INDEX(index), GC_gcj_kind, my_fl);
	    if (*my_fl == 0) return GC_oom_fn(bytes);
	    return GC_local_gcj_malloc(bytes, ptr_to_struct_containing_descr);
	}
    }
}

#endif /* GC_GCJ_SUPPORT */

# else  /* !THREAD_LOCAL_ALLOC  && !DBG_HDRS_ALL */

#   define GC_destroy_thread_local(t)

# endif /* !THREAD_LOCAL_ALLOC */

/*
 * We use signals to stop threads during GC.
 * 
 * Suspended threads wait in signal handler for SIG_THR_RESTART.
 * That's more portable than semaphores or condition variables.
 * (We do use sem_post from a signal handler, but that should be portable.)
 *
 * The thread suspension signal SIG_SUSPEND is now defined in gc_priv.h.
 * Note that we can't just stop a thread; we need it to save its stack
 * pointer(s) and acknowledge.
 */

#ifndef SIG_THR_RESTART
#  if defined(GC_HPUX_THREADS) || defined(GC_OSF1_THREADS)
#    ifdef _SIGRTMIN
#      define SIG_THR_RESTART _SIGRTMIN + 5
#    else
#      define SIG_THR_RESTART SIGRTMIN + 5
#    endif
#  else
#   define SIG_THR_RESTART SIGXCPU
#  endif
#endif

sem_t GC_suspend_ack_sem;

#if 0
/*
To make sure that we're using LinuxThreads and not some other thread
package, we generate a dummy reference to `pthread_kill_other_threads_np'
(was `__pthread_initial_thread_bos' but that disappeared),
which is a symbol defined in LinuxThreads, but (hopefully) not in other
thread packages.

We no longer do this, since this code is now portable enough that it might
actually work for something else.
*/
void (*dummy_var_to_force_linux_threads)() = pthread_kill_other_threads_np;
#endif /* 0 */

#if defined(SPARC) || defined(IA64)
  extern word GC_save_regs_in_stack();
#endif

long GC_nprocs = 1;	/* Number of processors.  We may not have	*/
			/* access to all of them, but this is as good	*/
			/* a guess as any ...				*/

#ifdef PARALLEL_MARK

# ifndef MAX_MARKERS
#   define MAX_MARKERS 16
# endif

static ptr_t marker_sp[MAX_MARKERS] = {0};

void * GC_mark_thread(void * id)
{
  word my_mark_no = 0;

  marker_sp[(word)id] = GC_approx_sp();
  for (;; ++my_mark_no) {
    /* GC_mark_no is passed only to allow GC_help_marker to terminate	*/
    /* promptly.  This is important if it were called from the signal	*/
    /* handler or from the GC lock acquisition code.  Under Linux, it's	*/
    /* not safe to call it from a signal handler, since it uses mutexes	*/
    /* and condition variables.  Since it is called only here, the 	*/
    /* argument is unnecessary.						*/
    if (my_mark_no < GC_mark_no || my_mark_no > GC_mark_no + 2) {
	/* resynchronize if we get far off, e.g. because GC_mark_no	*/
	/* wrapped.							*/
	my_mark_no = GC_mark_no;
    }
#   ifdef DEBUG_THREADS
	GC_printf1("Starting mark helper for mark number %ld\n", my_mark_no);
#   endif
    GC_help_marker(my_mark_no);
  }
}

extern long GC_markers;		/* Number of mark threads we would	*/
				/* like to have.  Includes the 		*/
				/* initiating thread.			*/

pthread_t GC_mark_threads[MAX_MARKERS];

#define PTHREAD_CREATE REAL_FUNC(pthread_create)

static void start_mark_threads()
{
    unsigned i;
    pthread_attr_t attr;

    if (GC_markers > MAX_MARKERS) {
	WARN("Limiting number of mark threads\n", 0);
	GC_markers = MAX_MARKERS;
    }
    if (0 != pthread_attr_init(&attr)) ABORT("pthread_attr_init failed");
	
    if (0 != pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED))
	ABORT("pthread_attr_setdetachstate failed");

#   if defined(HPUX) || defined(GC_DGUX386_THREADS)
      /* Default stack size is usually too small: fix it. */
      /* Otherwise marker threads or GC may run out of	  */
      /* space.						  */
#     define MIN_STACK_SIZE (8*HBLKSIZE*sizeof(word))
      {
	size_t old_size;
	int code;

        if (pthread_attr_getstacksize(&attr, &old_size) != 0)
	  ABORT("pthread_attr_getstacksize failed\n");
	if (old_size < MIN_STACK_SIZE) {
	  if (pthread_attr_setstacksize(&attr, MIN_STACK_SIZE) != 0)
		  ABORT("pthread_attr_setstacksize failed\n");
	}
      }
#   endif /* HPUX || GC_DGUX386_THREADS */
#   ifdef CONDPRINT
      if (GC_print_stats) {
	GC_printf1("Starting %ld marker threads\n", GC_markers - 1);
      }
#   endif
    for (i = 0; i < GC_markers - 1; ++i) {
      if (0 != PTHREAD_CREATE(GC_mark_threads + i, &attr,
			      GC_mark_thread, (void *)(word)i)) {
	WARN("Marker thread creation failed, errno = %ld.\n", errno);
      }
    }
}

#else  /* !PARALLEL_MARK */

static __inline__ void start_mark_threads()
{
}

#endif /* !PARALLEL_MARK */

void GC_suspend_handler(int sig)
{
    int dummy;
    pthread_t my_thread = pthread_self();
    GC_thread me;
    sigset_t all_sigs;
    sigset_t old_sigs;
    int i;
    sigset_t mask;
#   ifdef PARALLEL_MARK
	word my_mark_no = GC_mark_no;
	/* Marker can't proceed until we acknowledge.  Thus this is	*/
	/* guaranteed to be the mark_no correspending to our 		*/
	/* suspension, i.e. the marker can't have incremented it yet.	*/
#   endif
    word my_stop_count = GC_stop_count;

    if (sig != SIG_SUSPEND) ABORT("Bad signal in suspend_handler");

#if DEBUG_THREADS
    GC_printf1("Suspending 0x%lx\n", my_thread);
#endif

    me = GC_lookup_thread(my_thread);
    /* The lookup here is safe, since I'm doing this on behalf  */
    /* of a thread which holds the allocation lock in order	*/
    /* to stop the world.  Thus concurrent modification of the	*/
    /* data structure is impossible.				*/
    if (me -> last_stop_count == my_stop_count) {
	/* Duplicate signal.  OK if we are retrying.	*/
	if (!GC_retry_signals) {
	    WARN("Duplicate suspend signal in thread %lx\n",
		 pthread_self());
	}
	return;
    }
#   ifdef SPARC
	me -> stack_ptr = (ptr_t)GC_save_regs_in_stack();
#   else
	me -> stack_ptr = (ptr_t)(&dummy);
#   endif
#   ifdef IA64
	me -> backing_store_ptr = (ptr_t)GC_save_regs_in_stack();
#   endif

    /* Tell the thread that wants to stop the world that this   */
    /* thread has been stopped.  Note that sem_post() is  	*/
    /* the only async-signal-safe primitive in LinuxThreads.    */
    sem_post(&GC_suspend_ack_sem);
    me -> last_stop_count = my_stop_count;

    /* Wait until that thread tells us to restart by sending    */
    /* this thread a SIG_THR_RESTART signal.			*/
    /* SIG_THR_RESTART should be masked at this point.  Thus there	*/
    /* is no race.						*/
    if (sigfillset(&mask) != 0) ABORT("sigfillset() failed");
    if (sigdelset(&mask, SIG_THR_RESTART) != 0) ABORT("sigdelset() failed");
#   ifdef NO_SIGNALS
      if (sigdelset(&mask, SIGINT) != 0) ABORT("sigdelset() failed");
      if (sigdelset(&mask, SIGQUIT) != 0) ABORT("sigdelset() failed");
      if (sigdelset(&mask, SIGTERM) != 0) ABORT("sigdelset() failed");
      if (sigdelset(&mask, SIGABRT) != 0) ABORT("sigdelset() failed");
#   endif
    do {
	    me->signal = 0;
	    sigsuspend(&mask);             /* Wait for signal */
    } while (me->signal != SIG_THR_RESTART);
    /* If the RESTART signal gets lost, we can still lose.  That should be  */
    /* less likely than losing the SUSPEND signal, since we don't do much   */
    /* between the sem_post and sigsuspend.	   			    */
    /* We'd need more handshaking to work around that, since we don't want  */
    /* to accidentally leave a RESTART signal pending, thus causing us to   */
    /* continue prematurely in a future round.				    */ 

#if DEBUG_THREADS
    GC_printf1("Continuing 0x%lx\n", my_thread);
#endif
}

void GC_restart_handler(int sig)
{
    GC_thread me;

    if (sig != SIG_THR_RESTART) ABORT("Bad signal in suspend_handler");

    /* Let the GC_suspend_handler() know that we got a SIG_THR_RESTART. */
    /* The lookup here is safe, since I'm doing this on behalf  */
    /* of a thread which holds the allocation lock in order	*/
    /* to stop the world.  Thus concurrent modification of the	*/
    /* data structure is impossible.				*/
    me = GC_lookup_thread(pthread_self());
    me->signal = SIG_THR_RESTART;

    /*
    ** Note: even if we didn't do anything useful here,
    ** it would still be necessary to have a signal handler,
    ** rather than ignoring the signals, otherwise
    ** the signals will not be delivered at all, and
    ** will thus not interrupt the sigsuspend() above.
    */

#if DEBUG_THREADS
    GC_printf1("In GC_restart_handler for 0x%lx\n", pthread_self());
#endif
}

/* Defining INSTALL_LOOPING_SEGV_HANDLER causes SIGSEGV and SIGBUS to 	*/
/* result in an infinite loop in a signal handler.  This can be very	*/
/* useful for debugging, since (as of RH7) gdb still seems to have	*/
/* serious problems with threads.					*/
#ifdef INSTALL_LOOPING_SEGV_HANDLER
void GC_looping_handler(int sig)
{
    GC_printf3("Signal %ld in thread %lx, pid %ld\n",
	       sig, pthread_self(), getpid());
    for (;;);
}
#endif

GC_bool GC_thr_initialized = FALSE;

# define THREAD_TABLE_SZ 128	/* Must be power of 2	*/
volatile GC_thread GC_threads[THREAD_TABLE_SZ];

void GC_push_thread_structures GC_PROTO((void))
{
    GC_push_all((ptr_t)(GC_threads), (ptr_t)(GC_threads)+sizeof(GC_threads));
}

#ifdef THREAD_LOCAL_ALLOC
/* We must explicitly mark ptrfree and gcj free lists, since the free 	*/
/* list links wouldn't otherwise be found.  We also set them in the 	*/
/* normal free lists, since that involves touching less memory than if	*/
/* we scanned them normally.						*/
void GC_mark_thread_local_free_lists(void)
{
    int i, j;
    GC_thread p;
    ptr_t q;
    
    for (i = 0; i < THREAD_TABLE_SZ; ++i) {
      for (p = GC_threads[i]; 0 != p; p = p -> next) {
	for (j = 1; j < NFREELISTS; ++j) {
	  q = p -> ptrfree_freelists[j];
	  if ((word)q > HBLKSIZE) GC_set_fl_marks(q);
	  q = p -> normal_freelists[j];
	  if ((word)q > HBLKSIZE) GC_set_fl_marks(q);
#	  ifdef GC_GCJ_SUPPORT
	    q = p -> gcj_freelists[j];
	    if ((word)q > HBLKSIZE) GC_set_fl_marks(q);
#	  endif /* GC_GCJ_SUPPORT */
	}
      }
    }
}
#endif /* THREAD_LOCAL_ALLOC */

static struct GC_Thread_Rep first_thread;

/* Add a thread to GC_threads.  We assume it wasn't already there.	*/
/* Caller holds allocation lock.					*/
GC_thread GC_new_thread(pthread_t id)
{
    int hv = ((word)id) % THREAD_TABLE_SZ;
    GC_thread result;
    static GC_bool first_thread_used = FALSE;
    
    if (!first_thread_used) {
    	result = &first_thread;
    	first_thread_used = TRUE;
    } else {
        result = (struct GC_Thread_Rep *)
        	 GC_INTERNAL_MALLOC(sizeof(struct GC_Thread_Rep), NORMAL);
    }
    if (result == 0) return(0);
    result -> id = id;
    result -> next = GC_threads[hv];
    GC_threads[hv] = result;
    GC_ASSERT(result -> flags == 0 && result -> thread_blocked == 0);
    return(result);
}

/* Delete a thread from GC_threads.  We assume it is there.	*/
/* (The code intentionally traps if it wasn't.)			*/
/* Caller holds allocation lock.				*/
void GC_delete_thread(pthread_t id)
{
    int hv = ((word)id) % THREAD_TABLE_SZ;
    register GC_thread p = GC_threads[hv];
    register GC_thread prev = 0;
    
    while (!pthread_equal(p -> id, id)) {
        prev = p;
        p = p -> next;
    }
    if (prev == 0) {
        GC_threads[hv] = p -> next;
    } else {
        prev -> next = p -> next;
    }
    GC_INTERNAL_FREE(p);
}

/* If a thread has been joined, but we have not yet		*/
/* been notified, then there may be more than one thread 	*/
/* in the table with the same pthread id.			*/
/* This is OK, but we need a way to delete a specific one.	*/
void GC_delete_gc_thread(pthread_t id, GC_thread gc_id)
{
    int hv = ((word)id) % THREAD_TABLE_SZ;
    register GC_thread p = GC_threads[hv];
    register GC_thread prev = 0;

    while (p != gc_id) {
        prev = p;
        p = p -> next;
    }
    if (prev == 0) {
        GC_threads[hv] = p -> next;
    } else {
        prev -> next = p -> next;
    }
    GC_INTERNAL_FREE(p);
}

/* Return a GC_thread corresponding to a given thread_t.	*/
/* Returns 0 if it's not there.					*/
/* Caller holds  allocation lock or otherwise inhibits 		*/
/* updates.							*/
/* If there is more than one thread with the given id we 	*/
/* return the most recent one.					*/
GC_thread GC_lookup_thread(pthread_t id)
{
    int hv = ((word)id) % THREAD_TABLE_SZ;
    register GC_thread p = GC_threads[hv];
    
    while (p != 0 && !pthread_equal(p -> id, id)) p = p -> next;
    return(p);
}

#ifdef HANDLE_FORK
/* Remove all entries from the GC_threads table, except the	*/
/* one for the current thread.  We need to do this in the child	*/
/* process after a fork(), since only the current thread 	*/
/* survives in the child.					*/
void GC_remove_all_threads_but_me(void)
{
    pthread_t self = pthread_self();
    int hv;
    GC_thread p, next, me;

    for (hv = 0; hv < THREAD_TABLE_SZ; ++hv) {
      me = 0;
      for (p = GC_threads[hv]; 0 != p; p = next) {
	next = p -> next;
	if (p -> id == self) {
	  me = p;
	  p -> next = 0;
	} else {
#	  ifdef THREAD_LOCAL_ALLOC
	    if (!(p -> flags & FINISHED)) {
	      GC_destroy_thread_local(p);
	    }
#	  endif /* THREAD_LOCAL_ALLOC */
	  if (p != &first_thread) GC_INTERNAL_FREE(p);
	}
      }
      GC_threads[hv] = me;
    }
}
#endif /* HANDLE_FORK */

/* There seems to be a very rare thread stopping problem.  To help us  */
/* debug that, we save the ids of the stopping thread. */
pthread_t GC_stopping_thread;
int GC_stopping_pid;

/* We hold the allocation lock.  Suspend all threads that might	*/
/* still be running.  Return the number of suspend signals that	*/
/* were sent.							*/
int GC_suspend_all()
{
    int n_live_threads = 0;
    int i;
    GC_thread p;
    int result;
    pthread_t my_thread = pthread_self();

    GC_stopping_thread = my_thread;    /* debugging only.      */
    GC_stopping_pid = getpid();                /* debugging only.      */
    for (i = 0; i < THREAD_TABLE_SZ; i++) {
      for (p = GC_threads[i]; p != 0; p = p -> next) {
        if (p -> id != my_thread) {
            if (p -> flags & FINISHED) continue;
	    if (p -> last_stop_count == GC_stop_count) continue;
	    if (p -> thread_blocked) /* Will wait */ continue;
            n_live_threads++;
	    #if DEBUG_THREADS
	      GC_printf1("Sending suspend signal to 0x%lx\n", p -> id);
	    #endif
            result = pthread_kill(p -> id, SIG_SUSPEND);
	    switch(result) {
                case ESRCH:
                    /* Not really there anymore.  Possible? */
                    n_live_threads--;
                    break;
                case 0:
                    break;
                default:
                    ABORT("pthread_kill failed");
            }
        }
      }
    }
    return n_live_threads;
}

/* Caller holds allocation lock.	*/
void GC_stop_world()
{
    register int i;
    register int n_live_threads;

    /* Make sure all free list construction has stopped before we start. */
    /* No new construction can start, since free list construction is	*/
    /* required to acquire and release the GC lock before it starts,	*/
    /* and we have the lock.						*/
#   ifdef PARALLEL_MARK
      GC_acquire_mark_lock();
      GC_ASSERT(GC_fl_builder_count == 0);
      /* We should have previously waited for it to become zero. */
#   endif /* PARALLEL_MARK */
    ++GC_stop_count;
    n_live_threads = GC_suspend_all();
    if (GC_retry_signals) {
	unsigned long wait_usecs = 0;  /* Total wait since retry.	*/
#	define WAIT_UNIT 3000
#	define RETRY_INTERVAL 100000
	for (;;) {
	    int ack_count;

	    sem_getvalue(&GC_suspend_ack_sem, &ack_count);
	    if (ack_count == n_live_threads) break;
	    if (wait_usecs > RETRY_INTERVAL) {
		int newly_sent = GC_suspend_all();

#               ifdef CONDPRINT
                  if (GC_print_stats) {
		    GC_printf1("Resent %ld signals after timeout\n",
		               newly_sent);
	          }
#               endif
	        sem_getvalue(&GC_suspend_ack_sem, &ack_count);
		if (newly_sent < n_live_threads - ack_count) {
		    WARN("Lost some threads during GC_stop_world?!\n",0);
		    n_live_threads = ack_count + newly_sent;
		}
		wait_usecs = 0;
	    }
	    usleep(WAIT_UNIT);
	    wait_usecs += WAIT_UNIT;
	}
    }
    for (i = 0; i < n_live_threads; i++) {
    	if (0 != sem_wait(&GC_suspend_ack_sem))
	    ABORT("sem_wait in handler failed");
    }
#   ifdef PARALLEL_MARK
      GC_release_mark_lock();
#   endif
    #if DEBUG_THREADS
      GC_printf1("World stopped from 0x%lx\n", pthread_self());
    #endif
    GC_stopping_thread = 0;  /* debugging only */
}

/* Caller holds allocation lock, and has held it continuously since	*/
/* the world stopped.							*/
void GC_start_world()
{
    pthread_t my_thread = pthread_self();
    register int i;
    register GC_thread p;
    register int n_live_threads = 0;
    register int result;
    
#   if DEBUG_THREADS
      GC_printf0("World starting\n");
#   endif

    for (i = 0; i < THREAD_TABLE_SZ; i++) {
      for (p = GC_threads[i]; p != 0; p = p -> next) {
        if (p -> id != my_thread) {
            if (p -> flags & FINISHED) continue;
	    if (p -> thread_blocked) continue;
            n_live_threads++;
	    #if DEBUG_THREADS
	      GC_printf1("Sending restart signal to 0x%lx\n", p -> id);
	    #endif
            result = pthread_kill(p -> id, SIG_THR_RESTART);
	    switch(result) {
                case ESRCH:
                    /* Not really there anymore.  Possible? */
                    n_live_threads--;
                    break;
                case 0:
                    break;
                default:
                    ABORT("pthread_kill failed");
            }
        }
      }
    }
    #if DEBUG_THREADS
      GC_printf0("World started\n");
    #endif
}

# ifdef IA64
#   define IF_IA64(x) x
# else
#   define IF_IA64(x)
# endif
/* We hold allocation lock.  Should do exactly the right thing if the	*/
/* world is stopped.  Should not fail if it isn't.			*/
void GC_push_all_stacks()
{
    int i;
    GC_thread p;
    ptr_t sp = GC_approx_sp();
    ptr_t lo, hi;
    /* On IA64, we also need to scan the register backing store. */
    IF_IA64(ptr_t bs_lo; ptr_t bs_hi;)
    pthread_t me = pthread_self();
    
    if (!GC_thr_initialized) GC_thr_init();
    #if DEBUG_THREADS
        GC_printf1("Pushing stacks from thread 0x%lx\n", (unsigned long) me);
    #endif
    for (i = 0; i < THREAD_TABLE_SZ; i++) {
      for (p = GC_threads[i]; p != 0; p = p -> next) {
        if (p -> flags & FINISHED) continue;
        if (pthread_equal(p -> id, me)) {
#  	    ifdef SPARC
	        lo = (ptr_t)GC_save_regs_in_stack();
#  	    else
 	        lo = GC_approx_sp();
#           endif
	    IF_IA64(bs_hi = (ptr_t)GC_save_regs_in_stack();)
	} else {
	    lo = p -> stack_ptr;
	    IF_IA64(bs_hi = p -> backing_store_ptr;)
	}
        if ((p -> flags & MAIN_THREAD) == 0) {
	    hi = p -> stack_end;
	    IF_IA64(bs_lo = p -> backing_store_end);
        } else {
            /* The original stack. */
            hi = GC_stackbottom;
	    IF_IA64(bs_lo = BACKING_STORE_BASE;)
        }
        #if DEBUG_THREADS
            GC_printf3("Stack for thread 0x%lx = [%lx,%lx)\n",
    	        (unsigned long) p -> id,
		(unsigned long) lo, (unsigned long) hi);
        #endif
	if (0 == lo) ABORT("GC_push_all_stacks: sp not set!\n");
#       ifdef STACK_GROWS_UP
	  /* We got them backwards! */
          GC_push_all_stack(hi, lo);
#       else
          GC_push_all_stack(lo, hi);
#	endif
#	ifdef IA64
          if (pthread_equal(p -> id, me)) {
	    GC_push_all_eager(bs_lo, bs_hi);
	  } else {
	    GC_push_all_stack(bs_lo, bs_hi);
	  }
#	endif
      }
    }
}

#ifdef USE_PROC_FOR_LIBRARIES
int GC_segment_is_thread_stack(ptr_t lo, ptr_t hi)
{
    int i;
    GC_thread p;
    
#   ifdef PARALLEL_MARK
      for (i = 0; i < GC_markers; ++i) {
	if (marker_sp[i] > lo & marker_sp[i] < hi) return 1;
      }
#   endif
    for (i = 0; i < THREAD_TABLE_SZ; i++) {
      for (p = GC_threads[i]; p != 0; p = p -> next) {
	if (0 != p -> stack_end) {
#	  ifdef STACK_GROWS_UP
            if (p -> stack_end >= lo && p -> stack_end < hi) return 1;
#	  else /* STACK_GROWS_DOWN */
            if (p -> stack_end > lo && p -> stack_end <= hi) return 1;
#	  endif
	}
      }
    }
    return 0;
}
#endif /* USE_PROC_FOR_LIBRARIES */

#ifdef GC_LINUX_THREADS
/* Return the number of processors, or i<= 0 if it can't be determined.	*/
int GC_get_nprocs()
{
    /* Should be "return sysconf(_SC_NPROCESSORS_ONLN);" but that	*/
    /* appears to be buggy in many cases.				*/
    /* We look for lines "cpu<n>" in /proc/stat.			*/
#   define STAT_BUF_SIZE 4096
#   if defined(GC_USE_LD_WRAP)
#	define STAT_READ __real_read
#   else
#	define STAT_READ read
#   endif    
    char stat_buf[STAT_BUF_SIZE];
    int f;
    char c;
    word result = 1;
	/* Some old kernels only have a single "cpu nnnn ..."	*/
	/* entry in /proc/stat.  We identify those as 		*/
	/* uniprocessors.					*/
    size_t i, len = 0;

    f = open("/proc/stat", O_RDONLY);
    if (f < 0 || (len = STAT_READ(f, stat_buf, STAT_BUF_SIZE)) < 100) {
	WARN("Couldn't read /proc/stat\n", 0);
	return -1;
    }
    for (i = 0; i < len - 100; ++i) {
        if (stat_buf[i] == '\n' && stat_buf[i+1] == 'c'
	    && stat_buf[i+2] == 'p' && stat_buf[i+3] == 'u') {
	    int cpu_no = atoi(stat_buf + i + 4);
	    if (cpu_no >= result) result = cpu_no + 1;
	}
    }
    close(f);
    return result;
}
#endif /* GC_LINUX_THREADS */

/* We hold the GC lock.  Wait until an in-progress GC has finished.	*/
/* Repeatedly RELEASES GC LOCK in order to wait.			*/
/* If wait_for_all is true, then we exit with the GC lock held and no	*/
/* collection in progress; otherwise we just wait for the current GC	*/
/* to finish.								*/
void GC_wait_for_gc_completion(GC_bool wait_for_all)
{
    if (GC_incremental && GC_collection_in_progress()) {
	int old_gc_no = GC_gc_no;

	/* Make sure that no part of our stack is still on the mark stack, */
	/* since it's about to be unmapped.				   */
	while (GC_incremental && GC_collection_in_progress()
	       && (wait_for_all || old_gc_no == GC_gc_no)) {
	    ENTER_GC();
            GC_collect_a_little_inner(1);
	    EXIT_GC();
	    UNLOCK();
	    sched_yield();
	    LOCK();
	}
    }
}

#ifdef HANDLE_FORK
/* Procedures called before and after a fork.  The goal here is to make */
/* it safe to call GC_malloc() in a forked child.  It's unclear that is	*/
/* attainable, since the single UNIX spec seems to imply that one 	*/
/* should only call async-signal-safe functions, and we probably can't	*/
/* quite guarantee that.  But we give it our best shot.  (That same	*/
/* spec also implies that it's not safe to call the system malloc	*/
/* between fork() and exec().  Thus we're doing no worse than it.	*/

/* Called before a fork()		*/
void GC_fork_prepare_proc(void)
{
    /* Acquire all relevant locks, so that after releasing the locks	*/
    /* the child will see a consistent state in which monitor 		*/
    /* invariants hold.	 Unfortunately, we can't acquire libc locks	*/
    /* we might need, and there seems to be no guarantee that libc	*/
    /* must install a suitable fork handler.				*/
    /* Wait for an ongoing GC to finish, since we can't finish it in	*/
    /* the (one remaining thread in) the child.				*/
      LOCK();
#     if defined(PARALLEL_MARK) || defined(THREAD_LOCAL_ALLOC)
        GC_wait_for_reclaim();
#     endif
      GC_wait_for_gc_completion(TRUE);
#     if defined(PARALLEL_MARK) || defined(THREAD_LOCAL_ALLOC)
        GC_acquire_mark_lock();
#     endif
}

/* Called in parent after a fork()	*/
void GC_fork_parent_proc(void)
{
#   if defined(PARALLEL_MARK) || defined(THREAD_LOCAL_ALLOC)
      GC_release_mark_lock();
#   endif
    UNLOCK();
}

/* Called in child after a fork()	*/
void GC_fork_child_proc(void)
{
    /* Clean up the thread table, so that just our thread is left. */
#   if defined(PARALLEL_MARK) || defined(THREAD_LOCAL_ALLOC)
      GC_release_mark_lock();
#   endif
    GC_remove_all_threads_but_me();
#   ifdef PARALLEL_MARK
      /* Turn off parallel marking in the child, since we are probably 	*/
      /* just going to exec, and we would have to restart mark threads.	*/
        GC_markers = 1;
        GC_parallel = FALSE;
#   endif /* PARALLEL_MARK */
    UNLOCK();
}
#endif /* HANDLE_FORK */

#if defined(GC_DGUX386_THREADS)
/* Return the number of processors, or i<= 0 if it can't be determined. */
int GC_get_nprocs()
{
    /* <takis@XFree86.Org> */
    int numCpus;
    struct dg_sys_info_pm_info pm_sysinfo;
    int status =0;

    status = dg_sys_info((long int *) &pm_sysinfo,
	DG_SYS_INFO_PM_INFO_TYPE, DG_SYS_INFO_PM_CURRENT_VERSION);
    if (status < 0)
       /* set -1 for error */
       numCpus = -1;
    else
      /* Active CPUs */
      numCpus = pm_sysinfo.idle_vp_count;

#  ifdef DEBUG_THREADS
    GC_printf1("Number of active CPUs in this system: %d\n", numCpus);
#  endif
    return(numCpus);
}
#endif /* GC_DGUX386_THREADS */

/* We hold the allocation lock.	*/
void GC_thr_init()
{
    int dummy;
    GC_thread t;
    struct sigaction act;

    if (GC_thr_initialized) return;
    GC_thr_initialized = TRUE;

    if (sem_init(&GC_suspend_ack_sem, 0, 0) != 0)
    	ABORT("sem_init failed");

    act.sa_flags = SA_RESTART;
    if (sigfillset(&act.sa_mask) != 0) {
    	ABORT("sigfillset() failed");
    }
#   ifdef NO_SIGNALS
      if (sigdelset(&act.sa_mask, SIGINT) != 0
	  || sigdelset(&act.sa_mask, SIGQUIT != 0)
	  || sigdelset(&act.sa_mask, SIGABRT != 0)
	  || sigdelset(&act.sa_mask, SIGTERM != 0)) {
        ABORT("sigdelset() failed");
      }
#   endif

    /* SIG_THR_RESTART is unmasked by the handler when necessary. 	*/
    act.sa_handler = GC_suspend_handler;
    if (sigaction(SIG_SUSPEND, &act, NULL) != 0) {
    	ABORT("Cannot set SIG_SUSPEND handler");
    }

    act.sa_handler = GC_restart_handler;
    if (sigaction(SIG_THR_RESTART, &act, NULL) != 0) {
    	ABORT("Cannot set SIG_THR_RESTART handler");
    }
#   ifdef HANDLE_FORK
      /* Prepare for a possible fork.	*/
        pthread_atfork(GC_fork_prepare_proc, GC_fork_parent_proc,
	  	       GC_fork_child_proc);
#   endif /* HANDLE_FORK */
    /* Add the initial thread, so we can stop it.	*/
      t = GC_new_thread(pthread_self());
      t -> stack_ptr = (ptr_t)(&dummy);
      t -> flags = DETACHED | MAIN_THREAD;

    /* Check for GC_RETRY_SIGNALS.	*/
      if (0 != GETENV("GC_RETRY_SIGNALS")) {
	  GC_retry_signals = TRUE;
      }
      if (0 != GETENV("GC_NO_RETRY_SIGNALS")) {
	  GC_retry_signals = FALSE;
      }
#     ifdef CONDPRINT
          if (GC_print_stats) {
              GC_printf0("Will retry suspend signal if necessary.\n");
	  }
#     endif

    /* Set GC_nprocs.  */
      {
	char * nprocs_string = GETENV("GC_NPROCS");
	GC_nprocs = -1;
	if (nprocs_string != NULL) GC_nprocs = atoi(nprocs_string);
      }
      if (GC_nprocs <= 0) {
#       if defined(GC_HPUX_THREADS)
	  GC_nprocs = pthread_num_processors_np();
#       endif
#	if defined(GC_OSF1_THREADS)
	  GC_nprocs = sysconf(_SC_NPROCESSORS_ONLN);
	  if (GC_nprocs <= 0) GC_nprocs = 1;
#	endif
#       if defined(GC_FREEBSD_THREADS)
          GC_nprocs = 1;
#       endif
#	if defined(GC_LINUX_THREADS) || defined(GC_DGUX386_THREADS)
          GC_nprocs = GC_get_nprocs();
#	endif
      }
      if (GC_nprocs <= 0) {
	WARN("GC_get_nprocs() returned %ld\n", GC_nprocs);
	GC_nprocs = 2;
#	ifdef PARALLEL_MARK
	  GC_markers = 1;
#	endif
      } else {
#	ifdef PARALLEL_MARK
          {
	    char * markers_string = GETENV("GC_MARKERS");
	    if (markers_string != NULL) {
	      GC_markers = atoi(markers_string);
	    } else {
	      GC_markers = GC_nprocs;
	    }
          }
#	endif
      }
#   ifdef PARALLEL_MARK
#     ifdef CONDPRINT
        if (GC_print_stats) {
          GC_printf2("Number of processors = %ld, "
		 "number of marker threads = %ld\n", GC_nprocs, GC_markers);
	}
#     endif
      if (GC_markers == 1) {
	GC_parallel = FALSE;
#	ifdef CONDPRINT
	  if (GC_print_stats) {
	    GC_printf0("Single marker thread, turning off parallel marking\n");
	  }
#	endif
      } else {
	GC_parallel = TRUE;
	/* Disable true incremental collection, but generational is OK.	*/
	GC_time_limit = GC_TIME_UNLIMITED;
      }
#   endif
}


/* Perform all initializations, including those that	*/
/* may require allocation.				*/
/* Called without allocation lock.			*/
/* Must be called before a second thread is created.	*/
/* Called without allocation lock.			*/
void GC_init_parallel()
{
    if (parallel_initialized) return;
    parallel_initialized = TRUE;
    	/* GC_init() calls us back, so set flag first.	*/
    if (!GC_is_initialized) GC_init();
    /* If we are using a parallel marker, start the helper threads.  */
#     ifdef PARALLEL_MARK
        if (GC_parallel) start_mark_threads();
#     endif
    /* Initialize thread local free lists if used.	*/
#   if defined(THREAD_LOCAL_ALLOC) && !defined(DBG_HDRS_ALL)
      LOCK();
      GC_init_thread_local(GC_lookup_thread(pthread_self()));
      UNLOCK();
#   endif
}


int WRAP_FUNC(pthread_sigmask)(int how, const sigset_t *set, sigset_t *oset)
{
    sigset_t fudged_set;
    
    if (set != NULL && (how == SIG_BLOCK || how == SIG_SETMASK)) {
        fudged_set = *set;
        sigdelset(&fudged_set, SIG_SUSPEND);
        set = &fudged_set;
    }
    return(REAL_FUNC(pthread_sigmask)(how, set, oset));
}

/* Wrappers for functions that are likely to block for an appreciable	*/
/* length of time.  Must be called in pairs, if at all.			*/
/* Nothing much beyond the system call itself should be executed	*/
/* between these.							*/

void GC_start_blocking(void) {
#   define SP_SLOP 128
    GC_thread me;
    LOCK();
    me = GC_lookup_thread(pthread_self());
    GC_ASSERT(!(me -> thread_blocked));
#   ifdef SPARC
	me -> stack_ptr = (ptr_t)GC_save_regs_in_stack();
#   else
	me -> stack_ptr = (ptr_t)GC_approx_sp();
#   endif
#   ifdef IA64
	me -> backing_store_ptr = (ptr_t)GC_save_regs_in_stack() + SP_SLOP;
#   endif
    /* Add some slop to the stack pointer, since the wrapped call may 	*/
    /* end up pushing more callee-save registers.			*/
#   ifdef STACK_GROWS_UP
	me -> stack_ptr += SP_SLOP;
#   else
	me -> stack_ptr -= SP_SLOP;
#   endif
    me -> thread_blocked = TRUE;
    UNLOCK();
}

GC_end_blocking(void) {
    GC_thread me;
    LOCK();   /* This will block if the world is stopped.	*/
    me = GC_lookup_thread(pthread_self());
    GC_ASSERT(me -> thread_blocked);
    me -> thread_blocked = FALSE;
    UNLOCK();
}
    
#if defined(GC_DGUX386_THREADS)
#define __d10_sleep sleep
#endif /* GC_DGUX386_THREADS */

/* A wrapper for the standard C sleep function	*/
int WRAP_FUNC(sleep) (unsigned int seconds)
{
    int result;

    GC_start_blocking();
    result = REAL_FUNC(sleep)(seconds);
    GC_end_blocking();
    return result;
}

struct start_info {
    void *(*start_routine)(void *);
    void *arg;
    word flags;
    sem_t registered;   	/* 1 ==> in our thread table, but 	*/
				/* parent hasn't yet noticed.		*/
};

/* Called at thread exit.				*/
/* Never called for main thread.  That's OK, since it	*/
/* results in at most a tiny one-time leak.  And 	*/
/* linuxthreads doesn't reclaim the main threads 	*/
/* resources or id anyway.				*/
void GC_thread_exit_proc(void *arg)
{
    GC_thread me;

    LOCK();
    me = GC_lookup_thread(pthread_self());
    GC_destroy_thread_local(me);
    if (me -> flags & DETACHED) {
    	GC_delete_thread(pthread_self());
    } else {
	me -> flags |= FINISHED;
    }
#   if defined(THREAD_LOCAL_ALLOC) && !defined(USE_PTHREAD_SPECIFIC) \
       && !defined(USE_HPUX_TLS) && !defined(DBG_HDRS_ALL)
      GC_remove_specific(GC_thread_key);
#   endif
    GC_wait_for_gc_completion(FALSE);
    UNLOCK();
}

int WRAP_FUNC(pthread_join)(pthread_t thread, void **retval)
{
    int result;
    GC_thread thread_gc_id;
    
    LOCK();
    thread_gc_id = GC_lookup_thread(thread);
    /* This is guaranteed to be the intended one, since the thread id	*/
    /* cant have been recycled by pthreads.				*/
    UNLOCK();
    result = REAL_FUNC(pthread_join)(thread, retval);
# if defined (GC_FREEBSD_THREADS)
    /* On FreeBSD, the wrapped pthread_join() sometimes returns (what
       appears to be) a spurious EINTR which caused the test and real code
       to gratuitously fail.  Having looked at system pthread library source
       code, I see how this return code may be generated.  In one path of
       code, pthread_join() just returns the errno setting of the thread
       being joined.  This does not match the POSIX specification or the
       local man pages thus I have taken the liberty to catch this one
       spurious return value properly conditionalized on GC_FREEBSD_THREADS. */
    if (result == EINTR) result = 0;
# endif
    if (result == 0) {
        LOCK();
        /* Here the pthread thread id may have been recycled. */
        GC_delete_gc_thread(thread, thread_gc_id);
        UNLOCK();
    }
    return result;
}

int
WRAP_FUNC(pthread_detach)(pthread_t thread)
{
    int result;
    GC_thread thread_gc_id;
    
    LOCK();
    thread_gc_id = GC_lookup_thread(thread);
    UNLOCK();
    result = REAL_FUNC(pthread_detach)(thread);
    if (result == 0) {
      LOCK();
      thread_gc_id -> flags |= DETACHED;
      /* Here the pthread thread id may have been recycled. */
      if (thread_gc_id -> flags & FINISHED) {
        GC_delete_gc_thread(thread, thread_gc_id);
      }
      UNLOCK();
    }
    return result;
}

void * GC_start_routine(void * arg)
{
    int dummy;
    struct start_info * si = arg;
    void * result;
    GC_thread me;
    pthread_t my_pthread;
    void *(*start)(void *);
    void *start_arg;

    my_pthread = pthread_self();
#   ifdef DEBUG_THREADS
        GC_printf1("Starting thread 0x%lx\n", my_pthread);
        GC_printf1("pid = %ld\n", (long) getpid());
        GC_printf1("sp = 0x%lx\n", (long) &arg);
#   endif
    LOCK();
    me = GC_new_thread(my_pthread);
    me -> flags = si -> flags;
    me -> stack_ptr = 0;
    /* me -> stack_end = GC_linux_stack_base(); -- currently (11/99)	*/
    /* doesn't work because the stack base in /proc/self/stat is the 	*/
    /* one for the main thread.  There is a strong argument that that's	*/
    /* a kernel bug, but a pervasive one.				*/
#   ifdef STACK_GROWS_DOWN
      me -> stack_end = (ptr_t)(((word)(&dummy) + (GC_page_size - 1))
		                & ~(GC_page_size - 1));
      me -> stack_ptr = me -> stack_end - 0x10;
	/* Needs to be plausible, since an asynchronous stack mark	*/
	/* should not crash.						*/
#   else
      me -> stack_end = (ptr_t)((word)(&dummy) & ~(GC_page_size - 1));
      me -> stack_ptr = me -> stack_end + 0x10;
#   endif
    /* This is dubious, since we may be more than a page into the stack, */
    /* and hence skip some of it, though it's not clear that matters.	 */
#   ifdef IA64
      me -> backing_store_end = (ptr_t)
			(GC_save_regs_in_stack() & ~(GC_page_size - 1));
      /* This is also < 100% convincing.  We should also read this 	*/
      /* from /proc, but the hook to do so isn't there yet.		*/
#   endif /* IA64 */
    UNLOCK();
    start = si -> start_routine;
#   ifdef DEBUG_THREADS
	GC_printf1("start_routine = 0x%lx\n", start);
#   endif
    start_arg = si -> arg;
    sem_post(&(si -> registered));	/* Last action on si.	*/
    					/* OK to deallocate.	*/
    pthread_cleanup_push(GC_thread_exit_proc, 0);
#   if defined(THREAD_LOCAL_ALLOC) && !defined(DBG_HDRS_ALL)
 	LOCK();
        GC_init_thread_local(me);
	UNLOCK();
#   endif
    result = (*start)(start_arg);
#if DEBUG_THREADS
        GC_printf1("Finishing thread 0x%x\n", pthread_self());
#endif
    me -> status = result;
    me -> flags |= FINISHED;
    pthread_cleanup_pop(1);
    /* Cleanup acquires lock, ensuring that we can't exit		*/
    /* while a collection that thinks we're alive is trying to stop     */
    /* us.								*/
    return(result);
}

int
WRAP_FUNC(pthread_create)(pthread_t *new_thread,
		  const pthread_attr_t *attr,
                  void *(*start_routine)(void *), void *arg)
{
    int result;
    GC_thread t;
    pthread_t my_new_thread;
    int detachstate;
    word my_flags = 0;
    struct start_info * si; 
	/* This is otherwise saved only in an area mmapped by the thread */
	/* library, which isn't visible to the collector.		 */
 
    /* We resist the temptation to muck with the stack size here,	*/
    /* even if the default is unreasonably small.  That's the client's	*/
    /* responsibility.							*/

    LOCK();
    si = (struct start_info *)GC_INTERNAL_MALLOC(sizeof(struct start_info),
						 NORMAL);
    UNLOCK();
    if (!parallel_initialized) GC_init_parallel();
    if (0 == si) return(ENOMEM);
    sem_init(&(si -> registered), 0, 0);
    si -> start_routine = start_routine;
    si -> arg = arg;
    LOCK();
    if (!GC_thr_initialized) GC_thr_init();
    if (NULL == attr) {
	detachstate = PTHREAD_CREATE_JOINABLE;
    } else { 
        pthread_attr_getdetachstate(attr, &detachstate);
    }
    if (PTHREAD_CREATE_DETACHED == detachstate) my_flags |= DETACHED;
    si -> flags = my_flags;
    UNLOCK();
#   ifdef DEBUG_THREADS
        GC_printf1("About to start new thread from thread 0x%X\n",
		   pthread_self());
#   endif

    result = REAL_FUNC(pthread_create)(new_thread, attr, GC_start_routine, si);
#   ifdef DEBUG_THREADS
        GC_printf1("Started thread 0x%X\n", *new_thread);
#   endif
    /* Wait until child has been added to the thread table.		*/
    /* This also ensures that we hold onto si until the child is done	*/
    /* with it.  Thus it doesn't matter whether it is otherwise		*/
    /* visible to the collector.					*/
        while (0 != sem_wait(&(si -> registered))) {
	    if (EINTR != errno) ABORT("sem_wait failed");
	}
        sem_destroy(&(si -> registered));
	LOCK();
	GC_INTERNAL_FREE(si);
	UNLOCK();

    return(result);
}

#ifdef GENERIC_COMPARE_AND_SWAP
  pthread_mutex_t GC_compare_and_swap_lock = PTHREAD_MUTEX_INITIALIZER;

  GC_bool GC_compare_and_exchange(volatile GC_word *addr,
  			          GC_word old, GC_word new_val)
  {
    GC_bool result;
    pthread_mutex_lock(&GC_compare_and_swap_lock);
    if (*addr == old) {
      *addr = new_val;
      result = TRUE;
    } else {
      result = FALSE;
    }
    pthread_mutex_unlock(&GC_compare_and_swap_lock);
    return result;
  }
  
  GC_word GC_atomic_add(volatile GC_word *addr, GC_word how_much)
  {
    GC_word old;
    pthread_mutex_lock(&GC_compare_and_swap_lock);
    old = *addr;
    *addr = old + how_much;
    pthread_mutex_unlock(&GC_compare_and_swap_lock);
    return old;
  }

#endif /* GENERIC_COMPARE_AND_SWAP */
/* Spend a few cycles in a way that can't introduce contention with	*/
/* othre threads.							*/
void GC_pause()
{
    int i;
    volatile word dummy = 0;

    for (i = 0; i < 10; ++i) { 
#     ifdef __GNUC__
        __asm__ __volatile__ (" " : : : "memory");
#     else
	/* Something that's unlikely to be optimized away. */
	GC_noop(++dummy);
#     endif
    }
}
    
#define SPIN_MAX 1024	/* Maximum number of calls to GC_pause before	*/
			/* give up.					*/

VOLATILE GC_bool GC_collecting = 0;
			/* A hint that we're in the collector and       */
                        /* holding the allocation lock for an           */
                        /* extended period.                             */

#if !defined(USE_SPIN_LOCK) || defined(PARALLEL_MARK)
/* If we don't want to use the below spinlock implementation, either	*/
/* because we don't have a GC_test_and_set implementation, or because 	*/
/* we don't want to risk sleeping, we can still try spinning on 	*/
/* pthread_mutex_trylock for a while.  This appears to be very		*/
/* beneficial in many cases.						*/
/* I suspect that under high contention this is nearly always better	*/
/* than the spin lock.  But it's a bit slower on a uniprocessor.	*/
/* Hence we still default to the spin lock.				*/
/* This is also used to acquire the mark lock for the parallel		*/
/* marker.								*/

/* Here we use a strict exponential backoff scheme.  I don't know 	*/
/* whether that's better or worse than the above.  We eventually 	*/
/* yield by calling pthread_mutex_lock(); it never makes sense to	*/
/* explicitly sleep.							*/

void GC_generic_lock(pthread_mutex_t * lock)
{
    unsigned pause_length = 1;
    unsigned i;
    
    if (0 == pthread_mutex_trylock(lock)) return;
    for (; pause_length <= SPIN_MAX; pause_length <<= 1) {
	for (i = 0; i < pause_length; ++i) {
	    GC_pause();
	}
        switch(pthread_mutex_trylock(lock)) {
	    case 0:
		return;
	    case EBUSY:
		break;
	    default:
		ABORT("Unexpected error from pthread_mutex_trylock");
        }
    }
    pthread_mutex_lock(lock);
}

#endif /* !USE_SPIN_LOCK || PARALLEL_MARK */

#if defined(USE_SPIN_LOCK)

/* Reasonably fast spin locks.  Basically the same implementation */
/* as STL alloc.h.  This isn't really the right way to do this.   */
/* but until the POSIX scheduling mess gets straightened out ...  */

volatile unsigned int GC_allocate_lock = 0;


void GC_lock()
{
#   define low_spin_max 30  /* spin cycles if we suspect uniprocessor */
#   define high_spin_max SPIN_MAX /* spin cycles for multiprocessor */
    static unsigned spin_max = low_spin_max;
    unsigned my_spin_max;
    static unsigned last_spins = 0;
    unsigned my_last_spins;
    int i;

    if (!GC_test_and_set(&GC_allocate_lock)) {
        return;
    }
    my_spin_max = spin_max;
    my_last_spins = last_spins;
    for (i = 0; i < my_spin_max; i++) {
        if (GC_collecting || GC_nprocs == 1) goto yield;
        if (i < my_last_spins/2 || GC_allocate_lock) {
            GC_pause();
            continue;
        }
        if (!GC_test_and_set(&GC_allocate_lock)) {
	    /*
             * got it!
             * Spinning worked.  Thus we're probably not being scheduled
             * against the other process with which we were contending.
             * Thus it makes sense to spin longer the next time.
	     */
            last_spins = i;
            spin_max = high_spin_max;
            return;
        }
    }
    /* We are probably being scheduled against the other process.  Sleep. */
    spin_max = low_spin_max;
yield:
    for (i = 0;; ++i) {
        if (!GC_test_and_set(&GC_allocate_lock)) {
            return;
        }
#       define SLEEP_THRESHOLD 12
		/* Under Linux very short sleeps tend to wait until	*/
		/* the current time quantum expires.  On old Linux	*/
		/* kernels nanosleep(<= 2ms) just spins under Linux.    */
		/* (Under 2.4, this happens only for real-time		*/
		/* processes.)  We want to minimize both behaviors	*/
		/* here.						*/
        if (i < SLEEP_THRESHOLD) {
            sched_yield();
	} else {
	    struct timespec ts;
	
	    if (i > 24) i = 24;
			/* Don't wait for more than about 15msecs, even	*/
			/* under extreme contention.			*/
	    ts.tv_sec = 0;
	    ts.tv_nsec = 1 << i;
	    nanosleep(&ts, 0);
	}
    }
}

#else  /* !USE_SPINLOCK */

void GC_lock()
{
    if (1 == GC_nprocs || GC_collecting) {
	pthread_mutex_lock(&GC_allocate_ml);
    } else {
        GC_generic_lock(&GC_allocate_ml);
    }
}

#endif /* !USE_SPINLOCK */

#if defined(PARALLEL_MARK) || defined(THREAD_LOCAL_ALLOC)

#ifdef GC_ASSERTIONS
  pthread_t GC_mark_lock_holder = NO_THREAD;
#endif

#if 0
  /* Ugly workaround for a linux threads bug in the final versions      */
  /* of glibc2.1.  Pthread_mutex_trylock sets the mutex owner           */
  /* field even when it fails to acquire the mutex.  This causes        */
  /* pthread_cond_wait to die.  Remove for glibc2.2.                    */
  /* According to the man page, we should use                           */
  /* PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP, but that isn't actually   */
  /* defined.                                                           */
  static pthread_mutex_t mark_mutex =
        {0, 0, 0, PTHREAD_MUTEX_ERRORCHECK_NP, {0, 0}};
#else
  static pthread_mutex_t mark_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

static pthread_cond_t builder_cv = PTHREAD_COND_INITIALIZER;

void GC_acquire_mark_lock()
{
/*
    if (pthread_mutex_lock(&mark_mutex) != 0) {
	ABORT("pthread_mutex_lock failed");
    }
*/
    GC_generic_lock(&mark_mutex);
#   ifdef GC_ASSERTIONS
	GC_mark_lock_holder = pthread_self();
#   endif
}

void GC_release_mark_lock()
{
    GC_ASSERT(GC_mark_lock_holder == pthread_self());
#   ifdef GC_ASSERTIONS
	GC_mark_lock_holder = NO_THREAD;
#   endif
    if (pthread_mutex_unlock(&mark_mutex) != 0) {
	ABORT("pthread_mutex_unlock failed");
    }
}

/* Collector must wait for a freelist builders for 2 reasons:		*/
/* 1) Mark bits may still be getting examined without lock.		*/
/* 2) Partial free lists referenced only by locals may not be scanned 	*/
/*    correctly, e.g. if they contain "pointer-free" objects, since the	*/
/*    free-list link may be ignored.					*/
void GC_wait_builder()
{
    GC_ASSERT(GC_mark_lock_holder == pthread_self());
#   ifdef GC_ASSERTIONS
	GC_mark_lock_holder = NO_THREAD;
#   endif
    if (pthread_cond_wait(&builder_cv, &mark_mutex) != 0) {
	ABORT("pthread_cond_wait failed");
    }
    GC_ASSERT(GC_mark_lock_holder == NO_THREAD);
#   ifdef GC_ASSERTIONS
	GC_mark_lock_holder = pthread_self();
#   endif
}

void GC_wait_for_reclaim()
{
    GC_acquire_mark_lock();
    while (GC_fl_builder_count > 0) {
	GC_wait_builder();
    }
    GC_release_mark_lock();
}

void GC_notify_all_builder()
{
    GC_ASSERT(GC_mark_lock_holder == pthread_self());
    if (pthread_cond_broadcast(&builder_cv) != 0) {
	ABORT("pthread_cond_broadcast failed");
    }
}

#endif /* PARALLEL_MARK || THREAD_LOCAL_ALLOC */

#ifdef PARALLEL_MARK

static pthread_cond_t mark_cv = PTHREAD_COND_INITIALIZER;

void GC_wait_marker()
{
    GC_ASSERT(GC_mark_lock_holder == pthread_self());
#   ifdef GC_ASSERTIONS
	GC_mark_lock_holder = NO_THREAD;
#   endif
    if (pthread_cond_wait(&mark_cv, &mark_mutex) != 0) {
	ABORT("pthread_cond_wait failed");
    }
    GC_ASSERT(GC_mark_lock_holder == NO_THREAD);
#   ifdef GC_ASSERTIONS
	GC_mark_lock_holder = pthread_self();
#   endif
}

void GC_notify_all_marker()
{
    if (pthread_cond_broadcast(&mark_cv) != 0) {
	ABORT("pthread_cond_broadcast failed");
    }
}

#endif /* PARALLEL_MARK */

# endif /* GC_LINUX_THREADS and friends */

