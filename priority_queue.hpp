#pragma once

#include <limits>
#include <atomic>
#include <memory>
#include <iostream>

/* An implementation of a lock-free priority queue.
   Follows Michael and Scott memory management method.

   T is the Type pointer to hold
   K is the key type ( must allow > comparison )
*/

namespace lockfree {

  template< class T, typename K, typename = void >
  class _priority_queue {
  protected:
    struct Node { // pointer cleanup is managed by queue
      K key;
      std::atomic< int > counter; // reference count
      std::atomic< T * > value; // data ptr
      std::atomic< Node * > next;
      Node( ) : counter( 1 ), next( nullptr ) { };
      Node( K key, T *value ) : key( key ), value( value ), counter( 1 ), next( nullptr ) { }
    };

    std::atomic< Node * > free_list, head;
    Node *tail;

    template< class U >
    static inline U * get_marked( U *i ) {
      return reinterpret_cast< U * >( reinterpret_cast< uintptr_t >( i ) | 1 ); // 0x00000001
    };
    template< class U >
    static inline U * get_unmarked( U *i ) {
      return reinterpret_cast< U * >( reinterpret_cast< uintptr_t >( i ) &
				      std::numeric_limits< uintptr_t >::max( ) - 1 ); // 0xFFFFFFFE
    };
    template< class U >
    static inline bool is_marked( U *i ) {
      return ( reinterpret_cast< uintptr_t >( i ) & 1 ); // 0x00000001
    };

    _priority_queue( ) = default;
    _priority_queue( _priority_queue & ) = delete; // non-copyable

    // increase ref count -- if marked, then node is unsafe
    Node * safe_read( std::atomic< Node * > &node ) {
      while ( true ) {
	Node *read = node;
	if ( !read ) return nullptr; // node doesn't exist
	if ( is_marked( read ) ) return nullptr; // node is marked for deletion

	read->counter += 1;
	if ( read == node ) return read; // node didn't change during update so we have it
	release( read ); // read the wrong thing, so put it back
      }
    };
    // reclaim a node for the free list
    void reclaim( Node *node ) {
      Node *free_ptr;
      do {
	free_ptr = free_list;
	node->next = free_ptr; // add it to the front of the list
      } while ( !free_list.compare_exchange_weak( free_ptr, node ) );
    };
    // decrease ref count -- if necessary, destroy node
    void release( Node *node ) {
      int old_counter, new_counter;
      if ( !node ) return;

      do { // decrement counter and mark for reclaim if needed
	old_counter = node->counter;
	new_counter = old_counter - 1;
      } while ( !node->counter.compare_exchange_weak( old_counter, new_counter ) );
      if ( new_counter ) return; // if not claimed this round

      release( get_unmarked( node->next.load( ) ) ); // release next
      reclaim( node );
    };

    Node * get_new_node( T *value, K key ) {
      while ( true ) {
	Node *new_node, *free_ptr;
	new_node = free_ptr = safe_read( free_list ); // free_ptr may be changed by cxw
	if ( !new_node ) return new Node( key, value ); // this may be blocking
	if ( free_list.compare_exchange_weak( free_ptr, free_ptr->next ) ) {
	  new_node->counter += 1;
	  new_node->key = key;
	  new_node->value = value;
	  return new_node;
	} else {
	  release( new_node ); // someone else already checked this one out
	}
      }
    };
    Node * help_delete( Node *node ) {
      Node *next, *cxw, *prev = nullptr, *node_tmp = nullptr;
      bool assigned = false;
      do { // make sure next link is marked
	next = node->next;
      } while ( !is_marked( next ) && !node->next.compare_exchange_weak( next, get_marked( next ) ) );
      next = get_unmarked( next );
      if ( !next ) return safe_read( head ); // someone else already cleaned up
      do {
	release( prev );
	release( node_tmp );
	prev = safe_read( head );
	node_tmp = read_next( prev );
	while ( node_tmp != node && node_tmp != tail && !( node->key > node_tmp->key ) ) {
	  release( prev );
	  prev = node_tmp;
	  node_tmp = read_next( prev );
	} // find the node previously pointing to us or make sure it's gone
	cxw = node;
      } while ( node_tmp == node && !( assigned = prev->next.compare_exchange_strong( cxw, next ) ) );
      node->next = reinterpret_cast< Node * >( 1 ); // no extra ref to next
      if ( assigned ) release( node ); // prev's reference to node
      release( node_tmp ); // node_tmp used in this function
      return prev; // prev now has incremented count
    };
    // find the next node and return a reference to it
    Node * read_next( Node *node ) {
      Node *next;
      next = safe_read( node->next );
      while ( !next ) {
	node = help_delete( node );
	next = safe_read( node->next ); // safely read the next link
	release( node ); // help_delete gave us an extra ref
      }
      return next;
    };

#if defined DEBUG
    friend struct _priority_queue_test;
#endif
  public:
    void insert( T *value, K key ) {
      Node *prev, *node, *node_cxw;
      Node *new_node = get_new_node( value, key ); // starts referenced
      bool inserted;
      do {
	prev = safe_read( head );
	node = read_next( prev ); // start with head and next
	while ( !( key > node->key ) && node != tail ) { // find and check out the two nodes surrounding the insertion point
	  release( prev );
	  prev = node;
	  node = read_next( prev );
	} 
	new_node->next = node; // steal prev's reference to node
	node_cxw = node;
	inserted = prev->next.compare_exchange_weak( node_cxw, new_node ); // insert, on failure retry
	release( prev );
	release( node );
      } while ( !inserted );
    };

    T * pop( K key ) {
      Node *ret_node;
      T *ret;
      while ( ( ret_node = read_next( head ) ) ) {
	if ( key > ret_node->key || ret_node == tail ) { // if we reach the tail or low priority then abort
	  release( ret_node );
	  return nullptr;
	}
	ret = get_unmarked( ret_node->value ); // otherwise, we attempt to get an unmarked value
	if ( ret_node->value.compare_exchange_strong( ret, get_marked( ret ) ) ) {
	  release( ret_node );
	  return ret; // success
	} else { // already marked for deletion
	  release( help_delete( ret_node ) );
	  release( ret_node );
	}
      }
    };
    T * pop ( ) {
      Node *ret_node;
      T *ret;
      while ( ( ret_node = read_next( head ) ) ) {
	if ( ret_node == tail ) { // if we reach the tail
	  release( ret_node );
	  return nullptr;
	}
	ret = get_unmarked( ret_node->value.load( ) ); // otherwise, we attempt to get an unmarked value
	if ( ret_node->value.compare_exchange_strong( ret, get_marked( ret ) ) ) {
	  release( ret_node );
	  return ret; // success
	} else { // already marked for deletion
	  release( help_delete( ret_node ) );
	  release( ret_node );
	}
      }
      return nullptr; // we should reach tail before this
    };

    void reserve( std::size_t size ) {
      for ( std::size_t i; i < size; ++i ) {
	release( new Node( ) );
      }
      return;
    };
    
    ~_priority_queue( ) {
      T *item;
      while ( ( item = pop( ) ) ) { delete item; }; // clear list

      delete safe_read( head );
      delete tail;

      std::unique_ptr< Node > node( safe_read( free_list ) );
      while( node ) { node.reset( node->next ); }; // clean up nodes
      return;
    };
  };

  template< typename T, typename K, typename = void >
  class priority_queue : public _priority_queue< T, K > {
    typedef typename _priority_queue< T, K >::Node Node;
  public:
    priority_queue( ) : _priority_queue< T, K >( ) {
      this->free_list = nullptr;
      this->tail = new Node( K::min( ), nullptr );
      Node * new_head = new Node( K::max( ), nullptr );
      new_head->next = this->tail;
      this->head = new_head;
    };
  };
    
  template< typename T, typename K >
  class priority_queue< T, K, typename std::enable_if< std::is_fundamental< K >::value >::type >
    : public _priority_queue< T, K > {
    typedef typename _priority_queue< T, K >::Node Node;
  public:
    priority_queue( ) : _priority_queue< T, K >( ) {
      this->free_list = nullptr;
      this->tail = new Node( std::numeric_limits< K >::min( ), nullptr );
      Node * new_head = new Node( std::numeric_limits< K >::max( ), nullptr );
      new_head->next = this->tail;
      this->head = new_head;
    };
  };
  
}
