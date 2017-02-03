#include <stdio.h>
namespace std {}
using namespace std;
#include "BuildScript.h"

//=============================================================================
//  NativeCPP.cpp
//
//  Rogue runtime routines.
//=============================================================================

#include <fcntl.h>
#include <math.h>
#include <string.h>
#include <sys/timeb.h>
#include <sys/types.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <inttypes.h>
#include <exception>
#include <cstddef>

#if !defined(ROGUE_PLATFORM_WINDOWS)
#  include <sys/time.h>
#  include <unistd.h>
#  include <signal.h>
#  include <dirent.h>
#  include <sys/socket.h>
#  include <sys/uio.h>
#  include <sys/stat.h>
#  include <netdb.h>
#  include <errno.h>
#  include <pthread.h>
#endif

#if defined(ANDROID)
#  include <netinet/in.h>
#endif

#if defined(_WIN32)
#  include <direct.h>
#  define chdir _chdir
#endif

#if TARGET_OS_IPHONE
#  include <sys/types.h>
#  include <sys/sysctl.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#ifndef PATH_MAX
#  define PATH_MAX 4096
#endif

//-----------------------------------------------------------------------------
//  GLOBAL PROPERTIES
//-----------------------------------------------------------------------------
bool               Rogue_gc_logging   = false;
int                Rogue_gc_threshold = ROGUE_GC_THRESHOLD_DEFAULT;
bool               Rogue_gc_requested = false;
RogueLogical       Rogue_configured = 0;
int                Rogue_allocation_bytes_until_gc = Rogue_gc_threshold;
int                Rogue_argc;
const char**       Rogue_argv;
RogueDebugTrace*   Rogue_call_stack = 0;
RogueCallbackInfo  Rogue_on_gc_begin;
RogueCallbackInfo  Rogue_on_gc_trace_finished;
RogueCallbackInfo  Rogue_on_gc_end;
char               RogueDebugTrace::buffer[120];

struct RogueWeakReference;
RogueWeakReference* Rogue_weak_references = 0;

//-----------------------------------------------------------------------------
//  RogueDebugTrace
//-----------------------------------------------------------------------------
RogueDebugTrace::RogueDebugTrace( const char* method_signature, const char* filename, int line )
  : method_signature(method_signature), filename(filename), line(line), previous_trace(0)
{
  previous_trace = Rogue_call_stack;
  Rogue_call_stack = this;
}

RogueDebugTrace::~RogueDebugTrace()
{
  Rogue_call_stack = previous_trace;
}

int RogueDebugTrace::count()
{
  int n = 1;
  RogueDebugTrace* current = previous_trace;
  while (current)
  {
    ++n;
    current = current->previous_trace;
  }
  return n;
}

char* RogueDebugTrace::to_c_string()
{
  sprintf( buffer, "[%s %s:%d]", method_signature, filename, line );
  return buffer;
}

//-----------------------------------------------------------------------------
//  RogueType
//-----------------------------------------------------------------------------
RogueArray* RogueType_create_array( int count, int element_size, bool is_reference_array )
{
  if (count < 0) count = 0;
  int data_size  = count * element_size;
  int total_size = sizeof(RogueArray) + data_size;

  RogueArray* array = (RogueArray*) RogueAllocator_allocate_object( RogueTypeArray->allocator, RogueTypeArray, total_size );

  memset( array->as_bytes, 0, data_size );
  array->count = count;
  array->element_size = element_size;
  array->is_reference_array = is_reference_array;

  return array;
}

RogueObject* RogueType_create_object( RogueType* THIS, RogueInt32 size )
{
  ROGUE_DEF_LOCAL_REF_NULL(RogueObject*, obj);
  RogueInitFn  fn;

  obj = RogueAllocator_allocate_object( THIS->allocator, THIS, size ? size : THIS->object_size );

  if ((fn = THIS->init_object_fn)) return fn( obj );
  else                             return obj;
}

RogueString* RogueType_name( RogueType* THIS )
{
  return Rogue_literal_strings[ THIS->name_index ];
}

bool RogueType_name_equals( RogueType* THIS, const char* name )
{
  // For debugging purposes
  RogueString* st = Rogue_literal_strings[ THIS->name_index ];
  if ( !st ) return false;

  return (0 == strcmp((char*)st->utf8,name));
}

void RogueType_print_name( RogueType* THIS )
{
  RogueString* st = Rogue_literal_strings[ THIS->name_index ];
  if (st)
  {
    printf( "%s", st->utf8 );
  }
}

RogueType* RogueType_retire( RogueType* THIS )
{
  if (THIS->base_types)
  {
#if !ROGUE_GC_MODE_BOEHM
    delete [] THIS->base_types;
#endif
    THIS->base_types = 0;
    THIS->base_type_count = 0;
  }

  return THIS;
}

RogueObject* RogueType_singleton( RogueType* THIS )
{
  RogueInitFn fn;

  if (THIS->_singleton) return THIS->_singleton;

  // NOTE: _singleton must be assigned before calling init_object()
  // so we can't just call RogueType_create_object().
  THIS->_singleton = RogueAllocator_allocate_object( THIS->allocator, THIS, THIS->object_size );

  if ((fn = THIS->init_object_fn)) THIS->_singleton = fn( THIS->_singleton );

  if ((fn = THIS->init_fn)) return fn( THIS->_singleton );
  else                      return THIS->_singleton;

  return THIS->_singleton;
}

//-----------------------------------------------------------------------------
//  RogueObject
//-----------------------------------------------------------------------------
RogueObject* RogueObject_as( RogueObject* THIS, RogueType* specialized_type )
{
  if (RogueObject_instance_of(THIS,specialized_type)) return THIS;
  return 0;
}

RogueLogical RogueObject_instance_of( RogueObject* THIS, RogueType* ancestor_type )
{
  RogueType* this_type;

  if ( !THIS )
  {
    return false;
  }

  this_type = THIS->type;
  if (this_type == ancestor_type)
  {
    return true;
  }

  int count = this_type->base_type_count;
  RogueType** base_type_ptr = this_type->base_types - 1;
  while (--count >= 0)
  {
    if (ancestor_type == *(++base_type_ptr))
    {
      return true;
    }
  }

  return false;
}

void* RogueObject_retain( RogueObject* THIS )
{
  ROGUE_INCREF(THIS);
  return THIS;
}

void* RogueObject_release( RogueObject* THIS )
{
  ROGUE_DECREF(THIS);
  return THIS;
}

RogueString* RogueObject_to_string( RogueObject* THIS )
{
  RogueToStringFn fn = THIS->type->to_string_fn;
  if (fn) return fn( THIS );

  return Rogue_literal_strings[ THIS->type->name_index ];
}

void RogueObject_trace( void* obj )
{
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
}

void RogueString_trace( void* obj )
{
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
}

void RogueArray_trace( void* obj )
{
  int count;
  RogueObject** src;
  RogueArray* array = (RogueArray*) obj;

  if ( !array || array->object_size < 0 ) return;
  array->object_size = ~array->object_size;

  if ( !array->is_reference_array ) return;

  count = array->count;
  src = array->as_objects + count;
  while (--count >= 0)
  {
    RogueObject* cur = *(--src);
    if (cur && cur->object_size >= 0)
    {
      cur->type->trace_fn( cur );
    }
  }
}

//-----------------------------------------------------------------------------
//  RogueString
//-----------------------------------------------------------------------------
RogueString* RogueString_create_with_byte_count( int byte_count )
{
  if (byte_count < 0) byte_count = 0;

  int total_size = sizeof(RogueString) + (byte_count+1);

  RogueString* st = (RogueString*) RogueAllocator_allocate_object( RogueTypeString->allocator, RogueTypeString, total_size );
  st->byte_count = byte_count;

  return st;
}

RogueString* RogueString_create_from_utf8( const char* utf8, int count )
{
  if (count == -1) count = (int) strlen( utf8 );

  RogueString* st = RogueString_create_with_byte_count( count );
  memcpy( st->utf8, utf8, count );
  return RogueString_validate( st );
}

RogueString* RogueString_create_from_characters( RogueCharacter_List* characters )
{
  if ( !characters ) return RogueString_create_with_byte_count(0);

  RogueCharacter* data = characters->data->as_characters;
  int count = characters->count;
  int utf8_count = 0;
  for (int i=count; --i>=0; )
  {
    RogueCharacter ch = data[i];
    if (ch <= 0x7F)         ++utf8_count;
    else if (ch <= 0x7FF)   utf8_count += 2;
    else if (ch <= 0xFFFF)  utf8_count += 3;
    else                    utf8_count += 4;
  }

  RogueString* result = RogueString_create_with_byte_count( utf8_count );
  RogueByte*   dest = result->utf8;
  for (int i=0; i<count; ++i)
  {
    RogueCharacter ch = data[i];
    if (ch < 0)
    {
      *(dest++) = 0;
    }
    else if (ch <= 0x7F)
    {
      *(dest++) = (RogueByte) ch;
    }
    else if (ch <= 0x7FF)
    {
      dest[0] = (RogueByte) (0xC0 | ((ch >> 6) & 0x1F));
      dest[1] = (RogueByte) (0x80 | (ch & 0x3F));
      dest += 2;
    }
    else if (ch <= 0xFFFF)
    {
      dest[0] = (RogueByte) (0xE0 | ((ch >> 12) & 0xF));
      dest[1] = (RogueByte) (0x80 | ((ch >> 6) & 0x3F));
      dest[2] = (RogueByte) (0x80 | (ch & 0x3F));
      dest += 3;
    }
    else
    {
      dest[0] = (RogueByte) (0xF0 | ((ch >> 18) & 0x7));
      dest[1] = (RogueByte) (0x80 | ((ch >> 12) & 0x3F));
      dest[2] = (RogueByte) (0x80 | ((ch >> 6) & 0x3F));
      dest[3] = (RogueByte) (0x80 | (ch & 0x3F));
      dest += 4;
    }
  }

  result->character_count = count;

  return RogueString_validate( result );
}

void RogueString_print_string( RogueString* st )
{
  if (st)
  {
    RogueString_print_utf8( st->utf8, st->byte_count );
  }
  else
  {
    printf( "null" );
  }
}

void RogueString_print_characters( RogueCharacter* characters, int count )
{
  if (characters)
  {
    RogueCharacter* src = characters - 1;
    while (--count >= 0)
    {
      int ch = *(++src);

      if (ch < 0)
      {
        putchar( 0 );
      }
      else if (ch < 0x80)
      {
        // %0xxxxxxx
        putchar( ch );
      }
      else if (ch < 0x800)
      {
        // %110xxxxx 10xxxxxx
        putchar( ((ch >> 6) & 0x1f) | 0xc0 );
        putchar( (ch & 0x3f) | 0x80 );
      }
      else if (ch <= 0xFFFF)
      {
        // %1110xxxx 10xxxxxx 10xxxxxx
        putchar( ((ch >> 12) & 15) | 0xe0 );
        putchar( ((ch >> 6) & 0x3f) | 0x80 );
        putchar( (ch & 0x3f) | 0x80 );
      }
      else
      {
        // Assume 21-bit
        // %11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
        putchar( 0xf0 | ((ch>>18) & 7) );
        putchar( 0x80 | ((ch>>12) & 0x3f) );
        putchar( 0x80 | ((ch>>6)  & 0x3f) );
        putchar( (ch & 0x3f) | 0x80 );
      }
    }
  }
  else
  {
    printf( "null" );
  }
}

void RogueString_print_utf8( RogueByte* utf8, int count )
{
  --utf8;
  while (--count >= 0)
  {
    putchar( *(++utf8) );
  }
}

RogueCharacter RogueString_character_at( RogueString* THIS, int index )
{
  if (THIS->is_ascii) return (RogueCharacter) THIS->utf8[ index ];

  RogueInt32 offset = RogueString_set_cursor( THIS, index );
  RogueByte* utf8 = THIS->utf8;

  RogueCharacter ch = utf8[ offset ];
  if (ch & 0x80)
  {
    if (ch & 0x20)
    {
      if (ch & 0x10)
      {
        return ((ch&7)<<18)
            | ((utf8[offset+1] & 0x3F) << 12)
            | ((utf8[offset+2] & 0x3F) << 6)
            | (utf8[offset+3] & 0x3F);
      }
      else
      {
        return ((ch&15)<<12)
            | ((utf8[offset+1] & 0x3F) << 6)
            | (utf8[offset+2] & 0x3F);
      }
    }
    else
    {
      return ((ch&31)<<6)
          | (utf8[offset+1] & 0x3F);
    }
  }
  else
  {
    return ch;
  }
}

RogueInt32 RogueString_set_cursor( RogueString* THIS, int index )
{
  // Sets this string's cursor_offset and cursor_index and returns cursor_offset.
  if (THIS->is_ascii)
  {
    return THIS->cursor_offset = THIS->cursor_index = index;
  }

  RogueByte* utf8 = THIS->utf8;

  RogueInt32 c_offset;
  RogueInt32 c_index;
  if (index == 0)
  {
    THIS->cursor_index = 0;
    return THIS->cursor_offset = 0;
  }
  else if (index >= THIS->character_count - 1)
  {
    c_offset = THIS->byte_count;
    c_index = THIS->character_count;
  }
  else
  {
    c_offset  = THIS->cursor_offset;
    c_index = THIS->cursor_index;
  }

  while (c_index < index)
  {
    while ((utf8[++c_offset] & 0xC0) == 0x80) {}
    ++c_index;
  }

  while (c_index > index)
  {
    while ((utf8[--c_offset] & 0xC0) == 0x80) {}
    --c_index;
  }

  THIS->cursor_index = c_index;
  return THIS->cursor_offset = c_offset;
}

RogueString* RogueString_validate( RogueString* THIS )
{
  // Trims any invalid UTF-8, counts the number of characters, and sets the hash code
  THIS->is_ascii = 1;  // assumption

  int character_count = 0;
  int byte_count = THIS->byte_count;
  int i;
  RogueByte* utf8 = THIS->utf8;
  for (i=0; i<byte_count; ++character_count)
  {
    int b = utf8[ i ];
    if (b & 0x80)
    {
      THIS->is_ascii = 0;
      if ( !(b & 0x40) ) { break;}  // invalid UTF-8

      if (b & 0x20)
      {
        if (b & 0x10)
        {
          // %11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
          if (b & 0x08) { break;}
          if (i + 4 > byte_count || ((utf8[i+1] & 0xC0) != 0x80) || ((utf8[i+2] & 0xC0) != 0x80)
              || ((utf8[i+3] & 0xC0) != 0x80)) { break;}
          i += 4;
        }
        else
        {
          // %1110xxxx 10xxxxxx 10xxxxxx
          if (i + 3 > byte_count || ((utf8[i+1] & 0xC0) != 0x80) || ((utf8[i+2] & 0xC0) != 0x80)) { break;}
          i += 3;
        }
      }
      else
      {
        // %110x xxxx 10xx xxxx
        if (i + 2 > byte_count || ((utf8[i+1] & 0xC0) != 0x80)) { break; }
        i += 2;
      }
    }
    else
    {
      ++i;
    }
  }

  if (i != byte_count)
  {
    printf( "*** RogueString validation error - invalid UTF8 (%d/%d):\n", i, byte_count );
    printf( "%02x\n", utf8[0] );
    printf( "%s\n", utf8 );
    utf8[ i ] = 0;
    Rogue_print_stack_trace();
  }

  THIS->byte_count = i;
  THIS->character_count = character_count;

  int code = 0;
  int len = THIS->byte_count;
  RogueByte* src = THIS->utf8 - 1;
  while (--len >= 0)
  {
    code = ((code<<3) - code) + *(++src);
  }
  THIS->hash_code = code;
  return THIS;
}

//-----------------------------------------------------------------------------
//  RogueArray
//-----------------------------------------------------------------------------
RogueArray* RogueArray_set( RogueArray* THIS, RogueInt32 dest_i1, RogueArray* src_array, RogueInt32 src_i1, RogueInt32 copy_count )
{
  int element_size;
  int dest_i2, src_i2;

  if ( !src_array || dest_i1 >= THIS->count ) return THIS;
  if (THIS->is_reference_array ^ src_array->is_reference_array) return THIS;

  if (copy_count == -1) src_i2 = src_array->count - 1;
  else                  src_i2 = (src_i1 + copy_count) - 1;

  if (dest_i1 < 0)
  {
    src_i1 -= dest_i1;
    dest_i1 = 0;
  }

  if (src_i1 < 0) src_i1 = 0;
  if (src_i2 >= src_array->count) src_i2 = src_array->count - 1;
  if (src_i1 > src_i2) return THIS;

  copy_count = (src_i2 - src_i1) + 1;
  dest_i2 = dest_i1 + (copy_count - 1);
  if (dest_i2 >= THIS->count)
  {
    dest_i2 = (THIS->count - 1);
    copy_count = (dest_i2 - dest_i1) + 1;
  }
  if ( !copy_count ) return THIS;


#if defined(ROGUE_ARC)
  if (THIS != src_array || dest_i1 >= src_i1 + copy_count || (src_i1 + copy_count) <= dest_i1 || dest_i1 < src_i1)
  {
    // no overlap
    RogueObject** src  = src_array->as_objects + src_i1 - 1;
    RogueObject** dest = THIS->as_objects + dest_i1 - 1;
    while (--copy_count >= 0)
    {
      RogueObject* src_obj, dest_obj;
      if ((src_obj = *(++src))) ROGUE_INCREF(src_obj);
      if ((dest_obj = *(++dest)) && !(ROGUE_DECREF(dest_obj)))
      {
        // TODO: delete dest_obj
        *dest = src_obj;
      }
    }
  }
  else
  {
    // Copying earlier data to later data; copy in reverse order to
    // avoid accidental overwriting
    if (dest_i1 > src_i1)  // if they're equal then we don't need to copy anything!
    {
      RogueObject** src  = src_array->as_objects + src_i2 + 1;
      RogueObject** dest = THIS->as_objects + dest_i2 + 1;
      while (--copy_count >= 0)
      {
        RogueObject* src_obj, dest_obj;
        if ((src_obj = *(--src))) ROGUE_INCREF(src_obj);
        if ((dest_obj = *(--dest)) && !(ROGUE_DECREF(dest_obj)))
        {
          // TODO: delete dest_obj
          *dest = src_obj;
        }
      }
    }
  }
  return THIS;
#endif

  element_size = THIS->element_size;
  RogueByte* src = src_array->as_bytes + src_i1 * element_size;
  RogueByte* dest = THIS->as_bytes + (dest_i1 * element_size);
  int copy_bytes = copy_count * element_size;

  if (src == dest) return THIS;

  if (src >= dest + copy_bytes || (src + copy_bytes) <= dest)
  {
    // Copy region does not overlap
    memcpy( dest, src, copy_count * element_size );
  }
  else
  {
    // Copy region overlaps
    memmove( dest, src, copy_count * element_size );
  }

  return THIS;
}

//-----------------------------------------------------------------------------
//  RogueAllocationPage
//-----------------------------------------------------------------------------
RogueAllocationPage* RogueAllocationPage_create( RogueAllocationPage* next_page )
{
  RogueAllocationPage* result = (RogueAllocationPage*) ROGUE_NEW_BYTES(sizeof(RogueAllocationPage));
  result->next_page = next_page;
  result->cursor = result->data;
  result->remaining = ROGUEMM_PAGE_SIZE;
  return result;
}

RogueAllocationPage* RogueAllocationPage_delete( RogueAllocationPage* THIS )
{
  if (THIS) ROGUE_DEL_BYTES( THIS );
  return 0;
};

void* RogueAllocationPage_allocate( RogueAllocationPage* THIS, int size )
{
  // Round size up to multiple of 8.
  if (size > 0) size = (size + 7) & ~7;
  else          size = 8;

  if (size > THIS->remaining) return 0;

  //printf( "Allocating %d bytes from page.\n", size );
  void* result = THIS->cursor;
  THIS->cursor += size;
  THIS->remaining -= size;

  //printf( "%d / %d\n", ROGUEMM_PAGE_SIZE - remaining, ROGUEMM_PAGE_SIZE );
  return result;
}


//-----------------------------------------------------------------------------
//  RogueAllocator
//-----------------------------------------------------------------------------
RogueAllocator* RogueAllocator_create()
{
  RogueAllocator* result = (RogueAllocator*) ROGUE_NEW_BYTES( sizeof(RogueAllocator) );

  memset( result, 0, sizeof(RogueAllocator) );

  return result;
}

RogueAllocator* RogueAllocator_delete( RogueAllocator* THIS )
{
  while (THIS->pages)
  {
    RogueAllocationPage* next_page = THIS->pages->next_page;
    RogueAllocationPage_delete( THIS->pages );
    THIS->pages = next_page;
  }
  return 0;
}

void* RogueAllocator_allocate( RogueAllocator* THIS, int size )
{
#if ROGUE_GC_MODE_AUTO
  Rogue_collect_garbage();
#endif
  if (size > ROGUEMM_SMALL_ALLOCATION_SIZE_LIMIT)
  {
    Rogue_allocation_bytes_until_gc -= size;
    void * mem = ROGUE_NEW_BYTES(size);
#if ROGUE_GC_MODE_AUTO
    if (!mem)
    {
      // Try hard!
      Rogue_collect_garbage(true);
      mem = ROGUE_NEW_BYTES(size);
    }
#endif
    return mem;
  }

  size = (size > 0) ? (size + ROGUEMM_GRANULARITY_MASK) & ~ROGUEMM_GRANULARITY_MASK : ROGUEMM_GRANULARITY_SIZE;

  Rogue_allocation_bytes_until_gc -= size;

  int slot;
  ROGUE_DEF_LOCAL_REF(RogueObject*, obj, THIS->available_objects[(slot=(size>>ROGUEMM_GRANULARITY_BITS))]);

  if (obj)
  {
    //printf( "found free object\n");
    THIS->available_objects[slot] = obj->next_object;
    return obj;
  }

  // No free objects for requested size.

  // Try allocating a new object from the current page.
  if (THIS->pages )
  {
    obj = (RogueObject*) RogueAllocationPage_allocate( THIS->pages, size );
    if (obj) return obj;

    // Not enough room on allocation page.  Allocate any smaller blocks
    // we're able to and then move on to a new page.
    int s = slot - 1;
    while (s >= 1)
    {
      obj = (RogueObject*) RogueAllocationPage_allocate( THIS->pages, s << ROGUEMM_GRANULARITY_BITS );
      if (obj)
      {
        //printf( "free obj size %d\n", (s << ROGUEMM_GRANULARITY_BITS) );
        obj->next_object = THIS->available_objects[s];
        THIS->available_objects[s] = obj;
      }
      else
      {
        --s;
      }
    }
  }

  // New page; this will work for sure.
  THIS->pages = RogueAllocationPage_create( THIS->pages );
  return RogueAllocationPage_allocate( THIS->pages, size );
}

#if ROGUE_GC_MODE_BOEHM
void Rogue_Boehm_Finalizer( void* obj, void* data )
{
  RogueObject* o = (RogueObject*)obj;
  o->type->on_cleanup_fn(o);
}

RogueObject* RogueAllocator_allocate_object( RogueAllocator* THIS, RogueType* of_type, int size )
{
  // If we had more type information (e.g., whether the data contained
  // references), we could make better decisions here.
  // Also, it seems like we could probably use the small allocator too.
  RogueObject* obj = (RogueObject*)GC_MALLOC( size );
  if (!obj)
  {
    Rogue_collect_garbage( true );
    obj = (RogueObject*)GC_MALLOC( size );
  }
  ROGUE_GCDEBUG_STATEMENT( printf( "Allocating " ) );
  ROGUE_GCDEBUG_STATEMENT( RogueType_print_name(of_type) );
  ROGUE_GCDEBUG_STATEMENT( printf( " %p\n", (RogueObject*)obj ) );
  //ROGUE_GCDEBUG_STATEMENT( Rogue_print_stack_trace() );

  if (of_type->on_cleanup_fn)
  {
    GC_REGISTER_FINALIZER_IGNORE_SELF( obj, Rogue_Boehm_Finalizer, 0, 0, 0 );
  }

  memset( obj, 0, size );

  obj->type = of_type;
  obj->object_size = size;

  return obj;
}
#else
RogueObject* RogueAllocator_allocate_object( RogueAllocator* THIS, RogueType* of_type, int size )
{
  ROGUE_DEF_LOCAL_REF(RogueObject*, obj, (RogueObject*) RogueAllocator_allocate( THIS, size ));

  ROGUE_GCDEBUG_STATEMENT( printf( "Allocating " ) );
  ROGUE_GCDEBUG_STATEMENT( RogueType_print_name(of_type) );
  ROGUE_GCDEBUG_STATEMENT( printf( " %p\n", (RogueObject*)obj ) );
  //ROGUE_GCDEBUG_STATEMENT( Rogue_print_stack_trace() );

  memset( obj, 0, size );

  if (of_type->on_cleanup_fn)
  {
    obj->next_object = THIS->objects_requiring_cleanup;
    THIS->objects_requiring_cleanup = obj;
  }
  else
  {
    obj->next_object = THIS->objects;
    THIS->objects = obj;
  }
  obj->type = of_type;
  obj->object_size = size;

  return obj;
}
#endif

void* RogueAllocator_free( RogueAllocator* THIS, void* data, int size )
{
  if (data)
  {
    ROGUE_GCDEBUG_STATEMENT(memset(data,0,size));
    if (size > ROGUEMM_SMALL_ALLOCATION_SIZE_LIMIT)
    {
      ROGUE_DEL_BYTES( data );
    }
    else
    {
      // Return object to small allocation pool
      RogueObject* obj = (RogueObject*) data;
      int slot = (size + ROGUEMM_GRANULARITY_MASK) >> ROGUEMM_GRANULARITY_BITS;
      if (slot <= 0) slot = 1;
      obj->next_object = THIS->available_objects[slot];
      THIS->available_objects[slot] = obj;
    }
  }

  // Always returns null, allowing a pointer to be freed and assigned null in
  // a single step.
  return 0;
}


void RogueAllocator_free_objects( RogueAllocator* THIS )
{
  RogueObject* objects = THIS->objects;
  while (objects)
  {
    RogueObject* next_object = objects->next_object;
    RogueAllocator_free( THIS, objects, objects->object_size );
    objects = next_object;
  }

  THIS->objects = 0;
}

void RogueAllocator_collect_garbage( RogueAllocator* THIS )
{
  // Global program objects have already been traced through.

  // Trace through all as-yet unreferenced objects that are manually retained.
  RogueObject* cur = THIS->objects;
  while (cur)
  {
    if (cur->object_size >= 0 && cur->reference_count > 0)
    {
      cur->type->trace_fn( cur );
    }
    cur = cur->next_object;
  }

  cur = THIS->objects_requiring_cleanup;
  while (cur)
  {
    if (cur->object_size >= 0 && cur->reference_count > 0)
    {
      cur->type->trace_fn( cur );
    }
    cur = cur->next_object;
  }

  // For any unreferenced objects requiring clean-up, we'll:
  //   1.  Reference them and move them to a separate short-term list.
  //   2.  Finish the regular GC.
  //   3.  Call on_cleanup() on each of them, which may create new
  //       objects (which is why we have to wait until after the GC).
  //   4.  Move them to the list of regular objects.
  cur = THIS->objects_requiring_cleanup;
  RogueObject* unreferenced_on_cleanup_objects = 0;
  RogueObject* survivors = 0;  // local var for speed
  while (cur)
  {
    RogueObject* next_object = cur->next_object;
    if (cur->object_size < 0)
    {
      // Referenced.
      cur->object_size = ~cur->object_size;
      cur->next_object = survivors;
      survivors = cur;
    }
    else
    {
      // Unreferenced - go ahead and trace it since we'll call on_cleanup
      // on it.
      cur->type->trace_fn( cur );
      cur->next_object = unreferenced_on_cleanup_objects;
      unreferenced_on_cleanup_objects = cur;
    }
    cur = next_object;
  }
  THIS->objects_requiring_cleanup = survivors;

  // All objects are in a state where a non-negative size means that the object is
  // due to be deleted.
  Rogue_on_gc_trace_finished.call();

  // Reset or delete each general object
  cur = THIS->objects;
  THIS->objects = 0;
  survivors = 0;  // local var for speed

  while (cur)
  {
    RogueObject* next_object = cur->next_object;
    if (cur->object_size < 0)
    {
      cur->object_size = ~cur->object_size;
      cur->next_object = survivors;
      survivors = cur;
    }
    else
    {
      ROGUE_GCDEBUG_STATEMENT( printf( "Freeing " ) );
      ROGUE_GCDEBUG_STATEMENT( RogueType_print_name(cur->type) );
      ROGUE_GCDEBUG_STATEMENT( printf( " %p\n", cur ) );
      RogueAllocator_free( THIS, cur, cur->object_size );
    }
    cur = next_object;
  }

  THIS->objects = survivors;


  // Call on_cleanup() on unreferenced objects requiring cleanup
  // and move them to the general objects list so they'll be deleted
  // the next time they're unreferenced.  Calling on_cleanup() may
  // create additional objects so THIS->objects may change during a
  // on_cleanup() call.
  cur = unreferenced_on_cleanup_objects;
  while (cur)
  {
    RogueObject* next_object = cur->next_object;

    cur->type->on_cleanup_fn( cur );

    cur->object_size = ~cur->object_size;
    cur->next_object = THIS->objects;
    THIS->objects = cur;

    cur = next_object;
  }

  if (Rogue_gc_logging)
  {
    int byte_count = 0;
    int object_count = 0;

    for (int i=0; i<Rogue_allocator_count; ++i)
    {
      RogueAllocator* allocator = &Rogue_allocators[i];

      RogueObject* cur = allocator->objects;
      while (cur)
      {
        ++object_count;
        byte_count += cur->object_size;
        cur = cur->next_object;
      }

      cur = allocator->objects_requiring_cleanup;
      while (cur)
      {
        ++object_count;
        byte_count += cur->object_size;
        cur = cur->next_object;
      }
    }

    printf( "Post-GC: %d objects, %d bytes used.\n", object_count, byte_count );
  }
}

void Rogue_print_stack_trace ( bool leading_newline )
{
  RogueDebugTrace* current = Rogue_call_stack;
  if (current && leading_newline) printf( "\n" );
  while (current)
  {
    printf( "%s\n", current->to_c_string() );
    current = current->previous_trace;
  }
  printf("\n");
}

void Rogue_segfault_handler( int signal, siginfo_t *si, void *arg )
{
    if (si->si_addr < (void*)4096)
    {
      // Probably a null pointer dereference.
      printf( "Null reference error (accessing memory at %p)\n",
              si->si_addr );
    }
    else
    {
      if (si->si_code == SEGV_MAPERR)
        printf( "Access to unmapped memory at " );
      else if (si->si_code == SEGV_ACCERR)
        printf( "Access to forbidden memory at " );
      else
        printf( "Unknown segfault accessing " );
      printf("%p\n", si->si_addr);
    }

    Rogue_print_stack_trace( true );

    exit(1);
}

void Rogue_update_weak_references_during_gc()
{
  RogueWeakReference* cur = Rogue_weak_references;
  while (cur)
  {
    if (cur->value && cur->value->object_size >= 0)
    {
      // The value held by this weak reference is about to be deleted by the
      // GC system; null out the value.
      cur->value = 0;
    }
    cur = cur->next_weak_reference;
  }
}


void Rogue_configure_types()
{
  int i;
  int* type_info = Rogue_type_info_table;

  // Install seg fault handler
  struct sigaction sa;

  memset( &sa, 0, sizeof(sa) );
  sigemptyset( &sa.sa_mask );
  sa.sa_sigaction = Rogue_segfault_handler;
  sa.sa_flags     = SA_SIGINFO;

  sigaction( SIGSEGV, &sa, NULL );

  // Initialize allocators
  memset( Rogue_allocators, 0, sizeof(RogueAllocator)*Rogue_allocator_count );

#ifdef ROGUE_INTROSPECTION
  int global_property_pointer_cursor = 0;
  int property_offset_cursor = 0;
#endif

  // Initialize types
  for (i=0; i<Rogue_type_count; ++i)
  {
    int j;
    RogueType* type = &Rogue_types[i];

    memset( type, 0, sizeof(RogueType) );

    type->index = i;
    type->name_index = Rogue_type_name_index_table[i];
    type->object_size = Rogue_object_size_table[i];
#ifdef ROGUE_INTROSPECTION
    type->attributes = Rogue_attributes_table[i];
#endif
    type->allocator = &Rogue_allocators[ *(type_info++) ];
    type->methods = Rogue_dynamic_method_table + *(type_info++);
    type->base_type_count = *(type_info++);
    if (type->base_type_count)
    {
#if ROGUE_GC_MODE_BOEHM
      type->base_types = new (NoGC) RogueType*[ type->base_type_count ];
#else
      type->base_types = new RogueType*[ type->base_type_count ];
#endif
      for (j=0; j<type->base_type_count; ++j)
      {
        type->base_types[j] = &Rogue_types[ *(type_info++) ];
      }
    }

    type->global_property_count = *(type_info++);
    type->global_property_name_indices = type_info;
    type_info += type->global_property_count;
    type->global_property_type_indices = type_info;
    type_info += type->global_property_count;

    type->property_count = *(type_info++);
    type->property_name_indices = type_info;
    type_info += type->property_count;
    type->property_type_indices = type_info;
    type_info += type->property_count;

#ifdef ROGUE_INTROSPECTION
    if (((type->attributes & ROGUE_ATTRIBUTE_TYPE_MASK) == ROGUE_ATTRIBUTE_IS_CLASS)
      || ((type->attributes & ROGUE_ATTRIBUTE_TYPE_MASK) == ROGUE_ATTRIBUTE_IS_COMPOUND))
    {
      type->global_property_pointers = Rogue_global_property_pointers + global_property_pointer_cursor;
      global_property_pointer_cursor += type->global_property_count;
      type->property_offsets = Rogue_property_offsets + property_offset_cursor;
      property_offset_cursor += type->property_count;
    }
#endif

    type->trace_fn = Rogue_trace_fn_table[i];
    type->init_object_fn = Rogue_init_object_fn_table[i];
    type->init_fn        = Rogue_init_fn_table[i];
    type->on_cleanup_fn  = Rogue_on_cleanup_fn_table[i];
    type->to_string_fn   = Rogue_to_string_fn_table[i];
  }

  Rogue_on_gc_trace_finished.add( Rogue_update_weak_references_during_gc );
}

#if ROGUE_GC_MODE_BOEHM
static GC_ToggleRefStatus Rogue_Boehm_ToggleRefStatus( void * o )
{
  RogueObject* obj = (RogueObject*)o;
  if (obj->reference_count > 0) return GC_TOGGLE_REF_STRONG;
  return GC_TOGGLE_REF_DROP;
}

static void Rogue_Boehm_on_collection_event( GC_EventType event )
{
  if (event == GC_EVENT_START)
  {
    Rogue_on_gc_begin.call();
  }
  else if (event == GC_EVENT_END)
  {
    Rogue_on_gc_end.call();
  }
}

void Rogue_configure_gc()
{
  // Initialize Boehm collector
  //GC_set_finalize_on_demand(0);
  GC_set_toggleref_func(Rogue_Boehm_ToggleRefStatus);
  GC_set_on_collection_event(Rogue_Boehm_on_collection_event);
  //GC_set_all_interior_pointers(0);
  GC_INIT();
}
#else
void Rogue_configure_gc()
{
}
#endif

#if ROGUE_GC_MODE_BOEHM
bool Rogue_collect_garbage( bool forced )
{
  if (forced)
  {
    GC_gcollect();
    return true;
  }

  return GC_collect_a_little();
}
#else
bool Rogue_collect_garbage( bool forced )
{
  int i;

  if (Rogue_allocation_bytes_until_gc > 0 && !forced && !Rogue_gc_requested) return false;
  Rogue_gc_requested = false;

  Rogue_on_gc_begin.call();

//printf( "GC %d\n", Rogue_allocation_bytes_until_gc );
  Rogue_allocation_bytes_until_gc = Rogue_gc_threshold;

  Rogue_trace();

  for (i=0; i<Rogue_allocator_count; ++i)
  {
    RogueAllocator_collect_garbage( &Rogue_allocators[i] );
  }

  Rogue_on_gc_end.call();

  return true;
}
#endif

void Rogue_quit()
{
  int i;

  if ( !Rogue_configured ) return;
  Rogue_configured = 0;

  RogueGlobal__call_exit_functions( (RogueClassGlobal*) ROGUE_SINGLETON(Global) );

  // Give a few GC's to allow objects requiring clean-up to do so.
  Rogue_collect_garbage( true );
  Rogue_collect_garbage( true );
  Rogue_collect_garbage( true );

  for (i=0; i<Rogue_allocator_count; ++i)
  {
    RogueAllocator_free_objects( &Rogue_allocators[i] );
  }

  for (i=0; i<Rogue_type_count; ++i)
  {
    RogueType_retire( &Rogue_types[i] );
  }
}

#if ROGUE_GC_MODE_BOEHM

void Rogue_Boehm_IncRef (RogueObject* o)
{
  ++o->reference_count;
  if (o->reference_count == 1)
  {
    GC_toggleref_add(o, 1);
  }
}
void Rogue_Boehm_DecRef (RogueObject* o)
{
  --o->reference_count;
  if (o->reference_count < 0)
  {
    o->reference_count = 0;
  }
}
#endif


//-----------------------------------------------------------------------------
//  Exception handling
//-----------------------------------------------------------------------------
void Rogue_terminate_handler()
{
  printf( "Uncaught exception.\n" );
  exit(1);
}
typedef void(*ROGUEM0)(RogueObject*);
typedef RogueObject*(*ROGUEM1)(RogueObject*);
typedef RogueString*(*ROGUEM2)(RogueObject*);
typedef RogueClassGlobal*(*ROGUEM3)(RogueClassGlobal*);
typedef RogueString*(*ROGUEM4)(RogueClassGlobal*);
typedef RogueStringBuilder*(*ROGUEM5)(RogueStringBuilder*);
typedef RogueString*(*ROGUEM6)(RogueStringBuilder*);
typedef RogueByte_List*(*ROGUEM7)(RogueByte_List*);
typedef RogueString*(*ROGUEM8)(RogueByte_List*);
typedef RogueClassGenericList*(*ROGUEM9)(RogueClassGenericList*);
typedef RogueString*(*ROGUEM10)(RogueClassGenericList*);
typedef RogueString*(*ROGUEM11)(RogueArray*);
typedef RogueFunction___List*(*ROGUEM12)(RogueFunction___List*);
typedef RogueString*(*ROGUEM13)(RogueFunction___List*);
typedef RogueException*(*ROGUEM14)(RogueException*);
typedef RogueString*(*ROGUEM15)(RogueException*);
typedef RogueException*(*ROGUEM16)(RogueException*,RogueString*);
typedef RogueInt32(*ROGUEM17)(RogueString*);
typedef RogueString*(*ROGUEM18)(RogueString*);
typedef RogueClassStackTrace*(*ROGUEM19)(RogueClassStackTrace*);
typedef RogueString*(*ROGUEM20)(RogueClassStackTrace*);
typedef RogueString_List*(*ROGUEM21)(RogueString_List*);
typedef RogueString*(*ROGUEM22)(RogueString_List*);
typedef RogueCharacter_List*(*ROGUEM23)(RogueCharacter_List*);
typedef RogueString*(*ROGUEM24)(RogueCharacter_List*);
typedef RogueClassConsole*(*ROGUEM25)(RogueClassConsole*);
typedef RogueString*(*ROGUEM26)(RogueClassConsole*);
typedef RogueClassConsoleErrorPrinter*(*ROGUEM27)(RogueClassConsoleErrorPrinter*);
typedef RogueString*(*ROGUEM28)(RogueClassConsoleErrorPrinter*);
typedef RogueClassConsoleIOHandler*(*ROGUEM29)(RogueClassConsoleIOHandler*);
typedef RogueString*(*ROGUEM30)(RogueClassConsoleIOHandler*);
typedef void(*ROGUEM31)(RogueClassConsoleIOHandler*,RogueArray*,RogueInt32);
typedef RogueClassMath*(*ROGUEM32)(RogueClassMath*);
typedef RogueString*(*ROGUEM33)(RogueClassMath*);
typedef RogueClassRuntime*(*ROGUEM34)(RogueClassRuntime*);
typedef RogueString*(*ROGUEM35)(RogueClassRuntime*);
typedef RogueClassFunction_190*(*ROGUEM36)(RogueClassFunction_190*);
typedef RogueString*(*ROGUEM37)(RogueClassFunction_190*);
typedef RogueClassget_platform*(*ROGUEM38)(RogueClassget_platform*);
typedef RogueString*(*ROGUEM39)(RogueClassget_platform*);
typedef RogueClassstandard_build*(*ROGUEM40)(RogueClassstandard_build*);
typedef RogueString*(*ROGUEM41)(RogueClassstandard_build*);
typedef RogueClassSystem*(*ROGUEM42)(RogueClassSystem*);
typedef RogueString*(*ROGUEM43)(RogueClassSystem*);
typedef RogueClassError*(*ROGUEM44)(RogueClassError*);
typedef RogueString*(*ROGUEM45)(RogueClassError*);
typedef RogueWeakReference*(*ROGUEM46)(RogueWeakReference*);
typedef RogueString*(*ROGUEM47)(RogueWeakReference*);
typedef RogueClassFile*(*ROGUEM48)(RogueClassFile*);
typedef RogueString*(*ROGUEM49)(RogueClassFile*);
typedef RogueClassFunction_623*(*ROGUEM50)(RogueClassFunction_623*);
typedef RogueString*(*ROGUEM51)(RogueClassFunction_623*);
typedef RogueClassBlockingConsoleIOHandler*(*ROGUEM52)(RogueClassBlockingConsoleIOHandler*);
typedef RogueString*(*ROGUEM53)(RogueClassBlockingConsoleIOHandler*);
typedef void(*ROGUEM54)(RogueClassBlockingConsoleIOHandler*,RogueArray*,RogueInt32);
typedef RogueClassBuildConfig*(*ROGUEM55)(RogueClassBuildConfig*);
typedef RogueString*(*ROGUEM56)(RogueClassBuildConfig*);
typedef RogueClassinstall_emscripten*(*ROGUEM57)(RogueClassinstall_emscripten*);
typedef RogueString*(*ROGUEM58)(RogueClassinstall_emscripten*);
typedef RogueClassconfigure_build_folder*(*ROGUEM59)(RogueClassconfigure_build_folder*);
typedef RogueString*(*ROGUEM60)(RogueClassconfigure_build_folder*);
typedef RogueClasscompile*(*ROGUEM61)(RogueClasscompile*);
typedef RogueString*(*ROGUEM62)(RogueClasscompile*);
typedef RogueClassIOError*(*ROGUEM63)(RogueClassIOError*);
typedef RogueString*(*ROGUEM64)(RogueClassIOError*);
typedef RogueClassinstall_brew*(*ROGUEM65)(RogueClassinstall_brew*);
typedef RogueString*(*ROGUEM66)(RogueClassinstall_brew*);
typedef RogueClassinstall_library*(*ROGUEM67)(RogueClassinstall_library*);
typedef RogueString*(*ROGUEM68)(RogueClassinstall_library*);
typedef RogueClassneed_compile*(*ROGUEM69)(RogueClassneed_compile*);
typedef RogueString*(*ROGUEM70)(RogueClassneed_compile*);
typedef RogueClassmobile_or_desktop*(*ROGUEM71)(RogueClassmobile_or_desktop*);
typedef RogueString*(*ROGUEM72)(RogueClassmobile_or_desktop*);
typedef RogueClassrequire_command_line*(*ROGUEM73)(RogueClassrequire_command_line*);
typedef RogueString*(*ROGUEM74)(RogueClassrequire_command_line*);

RogueObject* Rogue_call_ROGUEM1( int i, RogueObject* THIS )
{
  return ((ROGUEM1)(THIS->type->methods[i]))( THIS );
}

RogueString* Rogue_call_ROGUEM2( int i, RogueObject* THIS )
{
  return ((ROGUEM2)(THIS->type->methods[i]))( THIS );
}

RogueString* Rogue_call_ROGUEM15( int i, RogueException* THIS )
{
  return ((ROGUEM15)(THIS->type->methods[i]))( THIS );
}

RogueException* Rogue_call_ROGUEM16( int i, RogueException* THIS, RogueString* p0 )
{
  return ((ROGUEM16)(THIS->type->methods[i]))( THIS, p0 );
}

void Rogue_call_ROGUEM31( int i, RogueClassConsoleIOHandler* THIS, RogueArray* p0, RogueInt32 p1 )
{
  ((ROGUEM31)(THIS->type->methods[i]))( THIS, p0, p1 );
}


// GLOBAL PROPERTIES
RogueByte_List* RogueStringBuilder_work_bytes = 0;
RogueString_List* RogueSystem_command_line_arguments = 0;
RogueString* RogueSystem_executable_filepath = 0;
RogueClassSystemEnvironment RogueSystem_environment = RogueClassSystemEnvironment();

void RogueGlobal_trace( void* obj );
void RogueStringBuilder_trace( void* obj );
void RogueByte_List_trace( void* obj );
void RogueFunction___List_trace( void* obj );
void RogueException_trace( void* obj );
void RogueStackTrace_trace( void* obj );
void RogueString_List_trace( void* obj );
void RogueCharacter_List_trace( void* obj );
void RogueConsole_trace( void* obj );
void RogueConsoleErrorPrinter_trace( void* obj );
void RogueError_trace( void* obj );
void RogueWeakReference_trace( void* obj );
void RogueFile_trace( void* obj );
void RogueFunction_623_trace( void* obj );
void RogueIOError_trace( void* obj );

void RogueGlobal_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueClassGlobal*)obj)->console)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=((RogueClassGlobal*)obj)->global_output_buffer)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=((RogueClassGlobal*)obj)->exit_functions)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueStringBuilder_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueStringBuilder*)obj)->utf8)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueByte_List_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueByte_List*)obj)->data)) RogueArray_trace( link );
}

void RogueFunction___List_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueFunction___List*)obj)->data)) RogueArray_trace( link );
}

void RogueException_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueException*)obj)->message)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=((RogueException*)obj)->stack_trace)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueStackTrace_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueClassStackTrace*)obj)->entries)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueString_List_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueString_List*)obj)->data)) RogueArray_trace( link );
}

void RogueCharacter_List_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueCharacter_List*)obj)->data)) RogueArray_trace( link );
}

void RogueConsole_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueClassConsole*)obj)->error)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=((RogueClassConsole*)obj)->output_buffer)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=((RogueClassConsole*)obj)->input_buffer)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=((RogueClassConsole*)obj)->io_handler)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueConsoleErrorPrinter_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueClassConsoleErrorPrinter*)obj)->output_buffer)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueError_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueClassError*)obj)->message)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=((RogueClassError*)obj)->stack_trace)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueWeakReference_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueWeakReference*)obj)->next_weak_reference)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueFile_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueClassFile*)obj)->filepath)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueFunction_623_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueClassFunction_623*)obj)->console)) ((RogueObject*)link)->type->trace_fn( link );
}

void RogueIOError_trace( void* obj )
{
  void* link;
  if ( !obj || ((RogueObject*)obj)->object_size < 0 ) return;
  ((RogueObject*)obj)->object_size = ~((RogueObject*)obj)->object_size;
  if ((link=((RogueClassIOError*)obj)->message)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=((RogueClassIOError*)obj)->stack_trace)) ((RogueObject*)link)->type->trace_fn( link );
}


int Rogue_type_name_index_table[] =
{
  11,73,111,112,77,100,76,113,106,78,114,115,103,116,105,6,
  75,74,102,104,117,118,119,101,107,79,120,121,87,88,80,81,
  82,83,84,85,108,86,89,90,109,91,92,93,94,110,95,96,
  97,98,99,122,123,124
};
RogueInitFn Rogue_init_object_fn_table[] =
{
  0,
  (RogueInitFn) RogueGlobal__init_object,
  0,
  0,
  (RogueInitFn) RogueStringBuilder__init_object,
  (RogueInitFn) RogueByte_List__init_object,
  (RogueInitFn) RogueGenericList__init_object,
  0,
  0,
  0,
  0,
  0,
  (RogueInitFn) RogueFunction___List__init_object,
  0,
  0,
  (RogueInitFn) RogueException__init_object,
  0,
  (RogueInitFn) RogueStackTrace__init_object,
  (RogueInitFn) RogueString_List__init_object,
  0,
  0,
  0,
  0,
  (RogueInitFn) RogueCharacter_List__init_object,
  0,
  (RogueInitFn) RogueConsole__init_object,
  0,
  0,
  (RogueInitFn) RogueConsoleErrorPrinter__init_object,
  (RogueInitFn) RogueConsoleIOHandler__init_object,
  (RogueInitFn) RogueMath__init_object,
  (RogueInitFn) RogueRuntime__init_object,
  (RogueInitFn) RogueFunction_190__init_object,
  (RogueInitFn) Rogueget_platform__init_object,
  (RogueInitFn) Roguestandard_build__init_object,
  (RogueInitFn) RogueSystem__init_object,
  (RogueInitFn) RogueError__init_object,
  (RogueInitFn) RogueWeakReference__init_object,
  (RogueInitFn) RogueFile__init_object,
  (RogueInitFn) RogueFunction_623__init_object,
  (RogueInitFn) RogueBlockingConsoleIOHandler__init_object,
  (RogueInitFn) RogueBuildConfig__init_object,
  (RogueInitFn) Rogueinstall_emscripten__init_object,
  (RogueInitFn) Rogueconfigure_build_folder__init_object,
  (RogueInitFn) Roguecompile__init_object,
  (RogueInitFn) RogueIOError__init_object,
  (RogueInitFn) Rogueinstall_brew__init_object,
  (RogueInitFn) Rogueinstall_library__init_object,
  (RogueInitFn) Rogueneed_compile__init_object,
  (RogueInitFn) Roguemobile_or_desktop__init_object,
  (RogueInitFn) Roguerequire_command_line__init_object,
  0,
  0,
  0
};

RogueInitFn Rogue_init_fn_table[] =
{
  0,
  (RogueInitFn) RogueGlobal__init,
  0,
  0,
  (RogueInitFn) RogueStringBuilder__init,
  (RogueInitFn) RogueByte_List__init,
  (RogueInitFn) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  (RogueInitFn) RogueFunction___List__init,
  0,
  0,
  (RogueInitFn) RogueException__init,
  0,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueString_List__init,
  0,
  0,
  0,
  0,
  (RogueInitFn) RogueCharacter_List__init,
  0,
  (RogueInitFn) RogueConsole__init,
  0,
  0,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueException__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueException__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  (RogueInitFn) RogueObject__init,
  0,
  0,
  0
};

RogueCleanUpFn Rogue_on_cleanup_fn_table[] =
{
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (RogueCleanUpFn) RogueWeakReference__on_cleanup,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0
};

RogueToStringFn Rogue_to_string_fn_table[] =
{
  0,
  (RogueToStringFn) RogueObject__to_String,
  0,
  0,
  (RogueToStringFn) RogueStringBuilder__to_String,
  (RogueToStringFn) RogueByte_List__to_String,
  (RogueToStringFn) RogueObject__to_String,
  0,
  0,
  0,
  0,
  0,
  (RogueToStringFn) RogueFunction___List__to_String,
  0,
  0,
  (RogueToStringFn) RogueException__to_String,
  0,
  (RogueToStringFn) RogueStackTrace__to_String,
  (RogueToStringFn) RogueString_List__to_String,
  0,
  0,
  0,
  0,
  (RogueToStringFn) RogueCharacter_List__to_String,
  0,
  (RogueToStringFn) RogueObject__to_String,
  0,
  0,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueException__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueFile__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueException__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  (RogueToStringFn) RogueObject__to_String,
  0,
  0,
  0
};

RogueTraceFn Rogue_trace_fn_table[] =
{
  RogueObject_trace,
  RogueGlobal_trace,
  0,
  0,
  RogueStringBuilder_trace,
  RogueByte_List_trace,
  RogueObject_trace,
  0,
  RogueObject_trace,
  RogueObject_trace,
  0,
  0,
  RogueFunction___List_trace,
  0,
  RogueObject_trace,
  RogueException_trace,
  RogueObject_trace,
  RogueStackTrace_trace,
  RogueString_List_trace,
  RogueObject_trace,
  0,
  0,
  0,
  RogueCharacter_List_trace,
  RogueObject_trace,
  RogueConsole_trace,
  0,
  0,
  RogueConsoleErrorPrinter_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueError_trace,
  RogueWeakReference_trace,
  RogueFile_trace,
  RogueFunction_623_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueIOError_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  RogueObject_trace,
  0,
  0,
  0
};

void Rogue_trace()
{
  void* link;
  int i;

  // Trace GLOBAL PROPERTIES
  if ((link=RogueStringBuilder_work_bytes)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=RogueSystem_command_line_arguments)) ((RogueObject*)link)->type->trace_fn( link );
  if ((link=RogueSystem_executable_filepath)) ((RogueObject*)link)->type->trace_fn( link );

  // Trace Class objects and singletons
  for (i=Rogue_type_count; --i>=0; )
  {
    RogueType* type = &Rogue_types[i];
    if (type->_singleton) type->trace_fn( type->_singleton );
  }
}

void* Rogue_dynamic_method_table[] =
{
  (void*) (ROGUEM0) RogueObject__init_object, // Object
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__type_name,
  (void*) (ROGUEM3) RogueGlobal__init_object, // Global
  (void*) (ROGUEM3) RogueGlobal__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM4) RogueGlobal__type_name,
  0, // PrintWriter<<global_output_buffer>>
  0, // PrintWriter
  (void*) (ROGUEM5) RogueStringBuilder__init_object, // StringBuilder
  (void*) (ROGUEM5) RogueStringBuilder__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM6) RogueStringBuilder__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM6) RogueStringBuilder__type_name,
  (void*) (ROGUEM7) RogueByte_List__init_object, // Byte[]
  (void*) (ROGUEM7) RogueByte_List__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM8) RogueByte_List__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM8) RogueByte_List__type_name,
  (void*) (ROGUEM9) RogueGenericList__init_object, // GenericList
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM10) RogueGenericList__type_name,
  (void*) (ROGUEM0) RogueObject__init_object, // Array<<Byte>>
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM11) RogueArray_Byte___type_name,
  (void*) (ROGUEM0) RogueObject__init_object, // NativeArray
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM11) RogueNativeArray__type_name,
  (void*) (ROGUEM12) RogueFunction___List__init_object, // Function()[]
  (void*) (ROGUEM12) RogueFunction___List__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM13) RogueFunction___List__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM13) RogueFunction___List__type_name,
  0, // Function()
  (void*) (ROGUEM0) RogueObject__init_object, // Array<<Function()>>
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM11) RogueArray_Function_____type_name,
  (void*) (ROGUEM14) RogueException__init_object, // Exception
  (void*) (ROGUEM14) RogueException__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM15) RogueException__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM15) RogueException__type_name,
  (void*) (ROGUEM16) RogueException__init__String,
  (void*) (ROGUEM0) RogueObject__init_object, // String
  (void*) (ROGUEM1) RogueObject__init,
  0,
  (void*) (ROGUEM17) RogueString__hash_code,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM18) RogueString__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM18) RogueString__type_name,
  (void*) (ROGUEM19) RogueStackTrace__init_object, // StackTrace
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM20) RogueStackTrace__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM20) RogueStackTrace__type_name,
  (void*) (ROGUEM21) RogueString_List__init_object, // String[]
  (void*) (ROGUEM21) RogueString_List__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM22) RogueString_List__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM22) RogueString_List__type_name,
  (void*) (ROGUEM0) RogueObject__init_object, // Array<<String>>
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM11) RogueArray_String___type_name,
  (void*) (ROGUEM23) RogueCharacter_List__init_object, // Character[]
  (void*) (ROGUEM23) RogueCharacter_List__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM24) RogueCharacter_List__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM24) RogueCharacter_List__type_name,
  (void*) (ROGUEM0) RogueObject__init_object, // Array<<Character>>
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM11) RogueArray_Character___type_name,
  (void*) (ROGUEM25) RogueConsole__init_object, // Console
  (void*) (ROGUEM25) RogueConsole__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM26) RogueConsole__type_name,
  0, // Reader<<Byte>>
  0, // PrintWriter<<output_buffer>>
  (void*) (ROGUEM27) RogueConsoleErrorPrinter__init_object, // ConsoleErrorPrinter
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM28) RogueConsoleErrorPrinter__type_name,
  (void*) (ROGUEM29) RogueConsoleIOHandler__init_object, // ConsoleIOHandler
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM30) RogueConsoleIOHandler__type_name,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM32) RogueMath__init_object, // Math
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM33) RogueMath__type_name,
  (void*) (ROGUEM34) RogueRuntime__init_object, // Runtime
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM35) RogueRuntime__type_name,
  (void*) (ROGUEM36) RogueFunction_190__init_object, // Function_190
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM37) RogueFunction_190__type_name,
  (void*) (ROGUEM38) Rogueget_platform__init_object, // get_platform
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM39) Rogueget_platform__type_name,
  (void*) (ROGUEM40) Roguestandard_build__init_object, // standard_build
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM41) Roguestandard_build__type_name,
  (void*) (ROGUEM42) RogueSystem__init_object, // System
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM43) RogueSystem__type_name,
  (void*) (ROGUEM44) RogueError__init_object, // Error
  (void*) (ROGUEM14) RogueException__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM15) RogueException__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM45) RogueError__type_name,
  (void*) (ROGUEM16) RogueException__init__String,
  (void*) (ROGUEM46) RogueWeakReference__init_object, // WeakReference
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM47) RogueWeakReference__type_name,
  (void*) (ROGUEM48) RogueFile__init_object, // File
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM49) RogueFile__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM49) RogueFile__type_name,
  (void*) (ROGUEM50) RogueFunction_623__init_object, // Function_623
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM51) RogueFunction_623__type_name,
  (void*) (ROGUEM52) RogueBlockingConsoleIOHandler__init_object, // BlockingConsoleIOHandler
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM53) RogueBlockingConsoleIOHandler__type_name,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM54) RogueBlockingConsoleIOHandler__write__Array_Int32,
  0,
  (void*) (ROGUEM54) RogueBlockingConsoleIOHandler__write_error__Array_Int32,
  (void*) (ROGUEM55) RogueBuildConfig__init_object, // BuildConfig
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM56) RogueBuildConfig__type_name,
  (void*) (ROGUEM57) Rogueinstall_emscripten__init_object, // install_emscripten
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM58) Rogueinstall_emscripten__type_name,
  (void*) (ROGUEM59) Rogueconfigure_build_folder__init_object, // configure_build_folder
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM60) Rogueconfigure_build_folder__type_name,
  (void*) (ROGUEM61) Roguecompile__init_object, // compile
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM62) Roguecompile__type_name,
  (void*) (ROGUEM63) RogueIOError__init_object, // IOError
  (void*) (ROGUEM14) RogueException__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM15) RogueException__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM64) RogueIOError__type_name,
  (void*) (ROGUEM16) RogueException__init__String,
  (void*) (ROGUEM65) Rogueinstall_brew__init_object, // install_brew
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM66) Rogueinstall_brew__type_name,
  (void*) (ROGUEM67) Rogueinstall_library__init_object, // install_library
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM68) Rogueinstall_library__type_name,
  (void*) (ROGUEM69) Rogueneed_compile__init_object, // need_compile
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM70) Rogueneed_compile__type_name,
  (void*) (ROGUEM71) Roguemobile_or_desktop__init_object, // mobile_or_desktop
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM72) Roguemobile_or_desktop__type_name,
  (void*) (ROGUEM73) Roguerequire_command_line__init_object, // require_command_line
  (void*) (ROGUEM1) RogueObject__init,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM2) RogueObject__to_String,
  0,
  0,
  0,
  0,
  (void*) (ROGUEM74) Roguerequire_command_line__type_name,

};

int Rogue_type_info_table[428] =
{
  // allocator_index, dynamic_method_table_index, base_class_count, base_class_index[base_class_count], ...
  0,0,0,0,0,0,17,3,0,2,3,0,3,125,126,127,3,4,12,0,34,1,3,0,
  0,0,35,0,0,0,0,36,1,0,1,128,5,6,129,130,131,132,133,134,5,10,10,10,10,
  11,0,53,2,6,0,0,2,135,130,8,10,0,70,1,0,0,0,0,0,0,0,0,0,87,
  2,9,0,0,0,0,104,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,121,2,6,
  0,0,2,135,130,14,10,0,138,0,0,0,0,139,2,9,0,0,0,0,156,1,0,0,2,
  136,137,16,17,0,174,1,0,0,0,0,191,1,0,0,3,138,130,139,18,10,11,0,208,2,
  6,0,0,2,135,130,19,10,0,225,2,9,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,242,2,6,0,0,2,135,130,24,10,0,259,2,9,0,0,0,0,276,
  4,0,26,27,3,0,7,140,141,142,143,144,145,146,10,28,4,4,51,29,21,0,293,0,0,
  1,140,10,0,294,1,3,0,0,0,295,3,0,27,3,0,1,142,4,0,312,1,0,0,0,
  0,336,1,0,0,0,0,353,1,0,0,0,0,370,2,0,13,0,0,0,387,1,0,0,0,
  0,404,1,0,0,0,0,421,1,0,3,147,148,149,18,16,52,0,0,438,2,15,0,0,2,
  136,137,16,17,0,456,1,0,0,2,150,151,37,21,0,473,1,0,0,1,152,16,0,490,2,
  0,13,0,1,125,25,0,507,2,29,0,0,1,144,51,0,531,1,0,0,1,153,11,0,548,
  1,0,0,0,0,565,1,0,0,0,0,582,1,0,0,0,0,599,3,36,15,0,0,2,136,
  137,16,17,0,617,1,0,0,0,0,634,1,0,0,0,0,651,1,0,0,0,0,668,1,0,
  0,0,0,685,1,0,0,0,0,0,0,0,2,154,155,10,11,0,0,0,0,0,0,0,0,
  0,1,156,10
};

int Rogue_object_size_table[54] =
{
  (int) sizeof(RogueObject),
  (int) sizeof(RogueClassGlobal),
  (int) sizeof(RogueClassPrintWriter_global_output_buffer_),
  (int) sizeof(RogueClassPrintWriter),
  (int) sizeof(RogueStringBuilder),
  (int) sizeof(RogueByte_List),
  (int) sizeof(RogueClassGenericList),
  (int) sizeof(RogueByte),
  (int) sizeof(RogueArray),
  (int) sizeof(RogueArray),
  (int) sizeof(RogueInt32),
  (int) sizeof(RogueLogical),
  (int) sizeof(RogueFunction___List),
  (int) sizeof(RogueClassFunction__),
  (int) sizeof(RogueArray),
  (int) sizeof(RogueException),
  (int) sizeof(RogueString),
  (int) sizeof(RogueClassStackTrace),
  (int) sizeof(RogueString_List),
  (int) sizeof(RogueArray),
  (int) sizeof(RogueReal64),
  (int) sizeof(RogueInt64),
  (int) sizeof(RogueCharacter),
  (int) sizeof(RogueCharacter_List),
  (int) sizeof(RogueArray),
  (int) sizeof(RogueClassConsole),
  (int) sizeof(RogueClassReader_Byte_),
  (int) sizeof(RogueClassPrintWriter_output_buffer_),
  (int) sizeof(RogueClassConsoleErrorPrinter),
  (int) sizeof(RogueClassConsoleIOHandler),
  (int) sizeof(RogueClassMath),
  (int) sizeof(RogueClassRuntime),
  (int) sizeof(RogueClassFunction_190),
  (int) sizeof(RogueClassget_platform),
  (int) sizeof(RogueClassstandard_build),
  (int) sizeof(RogueClassSystem),
  (int) sizeof(RogueClassError),
  (int) sizeof(RogueWeakReference),
  (int) sizeof(RogueClassFile),
  (int) sizeof(RogueClassFunction_623),
  (int) sizeof(RogueClassBlockingConsoleIOHandler),
  (int) sizeof(RogueClassBuildConfig),
  (int) sizeof(RogueClassinstall_emscripten),
  (int) sizeof(RogueClassconfigure_build_folder),
  (int) sizeof(RogueClasscompile),
  (int) sizeof(RogueClassIOError),
  (int) sizeof(RogueClassinstall_brew),
  (int) sizeof(RogueClassinstall_library),
  (int) sizeof(RogueClassneed_compile),
  (int) sizeof(RogueClassmobile_or_desktop),
  (int) sizeof(RogueClassrequire_command_line),
  (int) sizeof(RogueOptionalInt32),
  (int) sizeof(RogueClassSystemEnvironment),
  (int) sizeof(RogueClassFileOptions)
};

int Rogue_allocator_count = 1;
RogueAllocator Rogue_allocators[1];

int Rogue_type_count = 54;
RogueType Rogue_types[54];

RogueType* RogueTypeObject;
RogueType* RogueTypeGlobal;
RogueType* RogueTypePrintWriter_global_output_buffer_;
RogueType* RogueTypePrintWriter;
RogueType* RogueTypeStringBuilder;
RogueType* RogueTypeByte_List;
RogueType* RogueTypeGenericList;
RogueType* RogueTypeByte;
RogueType* RogueTypeArray;
RogueType* RogueTypeInt32;
RogueType* RogueTypeLogical;
RogueType* RogueTypeFunction___List;
RogueType* RogueTypeFunction__;
RogueType* RogueTypeException;
RogueType* RogueTypeString;
RogueType* RogueTypeStackTrace;
RogueType* RogueTypeString_List;
RogueType* RogueTypeReal64;
RogueType* RogueTypeInt64;
RogueType* RogueTypeCharacter;
RogueType* RogueTypeCharacter_List;
RogueType* RogueTypeConsole;
RogueType* RogueTypeReader_Byte_;
RogueType* RogueTypePrintWriter_output_buffer_;
RogueType* RogueTypeConsoleErrorPrinter;
RogueType* RogueTypeConsoleIOHandler;
RogueType* RogueTypeMath;
RogueType* RogueTypeRuntime;
RogueType* RogueTypeFunction_190;
RogueType* RogueTypeget_platform;
RogueType* RogueTypestandard_build;
RogueType* RogueTypeSystem;
RogueType* RogueTypeError;
RogueType* RogueTypeWeakReference;
RogueType* RogueTypeFile;
RogueType* RogueTypeFunction_623;
RogueType* RogueTypeBlockingConsoleIOHandler;
RogueType* RogueTypeBuildConfig;
RogueType* RogueTypeinstall_emscripten;
RogueType* RogueTypeconfigure_build_folder;
RogueType* RogueTypecompile;
RogueType* RogueTypeIOError;
RogueType* RogueTypeinstall_brew;
RogueType* RogueTypeinstall_library;
RogueType* RogueTypeneed_compile;
RogueType* RogueTypemobile_or_desktop;
RogueType* RogueTyperequire_command_line;
RogueType* RogueTypeOptionalInt32;
RogueType* RogueTypeSystemEnvironment;
RogueType* RogueTypeFileOptions;

int Rogue_literal_string_count = 157;
RogueString* Rogue_literal_strings[157];

void RogueStringBuilder__init_class()
{
  RogueStringBuilder_work_bytes = ((RogueByte_List__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueByte_List*,ROGUE_CREATE_OBJECT(Byte_List))) )));
}

RogueLogical RogueString__operatorEQUALSEQUALS__String_String( RogueString* a_0, RogueString* b_1 )
{
  if (((void*)a_0) == ((void*)NULL))
  {
    return (RogueLogical)(((void*)b_1) == ((void*)NULL));
  }
  else
  {
    return (RogueLogical)(((RogueString__operatorEQUALSEQUALS__String( a_0, b_1 ))));
  }
}

RogueString* RogueString__operatorPLUS__String_String( RogueString* st_0, RogueString* value_1 )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,_auto_29_2,(st_0));
  return (RogueString*)(((RogueString__operatorPLUS__String( ROGUE_ARG(((((_auto_29_2))) ? (ROGUE_ARG(_auto_29_2)) : ROGUE_ARG(Rogue_literal_strings[1]))), value_1 ))));
}

RogueString* RogueString__operatorTIMES__String_Int32( RogueString* st_0, RogueInt32 value_1 )
{
  if (((void*)st_0) == ((void*)NULL))
  {
    return (RogueString*)(((RogueString*)(NULL)));
  }
  return (RogueString*)(((RogueString__times__Int32( st_0, value_1 ))));
}

RogueCharacter RogueCharacter__create__Int32( RogueInt32 value_0 )
{
  return (RogueCharacter)(((RogueCharacter)(value_0)));
}

RogueString* RogueConsole__input__String( RogueString* prompt_0 )
{
  if (!!(prompt_0))
  {
    RogueGlobal__flush( ROGUE_ARG(((RogueGlobal__print__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), prompt_0 )))) );
  }
  char st[4096];
  fgets( st, 4096, stdin );
  // discard \n
  int len = strlen( st );
  if (len) st[--len] = 0;
  return RogueString_create_from_utf8( st, len );

}

RogueInt32 RogueMath__max__Int32_Int32( RogueInt32 a_0, RogueInt32 b_1 )
{
  if (a_0 >= b_1)
  {
    return (RogueInt32)(a_0);
  }
  else
  {
    return (RogueInt32)(b_1);
  }
}

RogueInt64 RogueMath__mod__Int64_Int64( RogueInt64 a_0, RogueInt64 b_1 )
{
  if (((((!(!!(a_0))) && (!(!!(b_1))))) || (b_1 == 1LL)))
  {
    return (RogueInt64)(0LL);
  }
  RogueInt64 r_2 = (a_0 % b_1);
  if (((a_0) ^ (b_1)) < 0LL)
  {
    if (!!(r_2))
    {
      return (RogueInt64)(((r_2) + (b_1)));
    }
    else
    {
      return (RogueInt64)(0LL);
    }
  }
  else
  {
    return (RogueInt64)(r_2);
  }
}

void RogueRuntime__init_class()
{
  ROGUE_DEF_LOCAL_REF(RogueString*,value_0,(((RogueSystemEnvironment__get__String( ROGUE_ARG(RogueSystem_environment), Rogue_literal_strings[70] )))));
  if (((void*)value_0) != ((void*)NULL))
  {
    RogueReal64 n_1 = (strtod( (char*)value_0->utf8, 0 ));
    if (((((RogueString__ends_with__Character( value_0, (RogueCharacter)'M' )))) || (((RogueString__ends_with__String( value_0, Rogue_literal_strings[71] ))))))
    {
      n_1 *= 1048576.0;
    }
    else if (((((RogueString__ends_with__Character( value_0, (RogueCharacter)'K' )))) || (((RogueString__ends_with__String( value_0, Rogue_literal_strings[72] ))))))
    {
      n_1 *= 1024.0;
    }
    RogueRuntime__set_gc_threshold__Int32( ROGUE_ARG(((RogueInt32)(n_1))) );
  }
}

void RogueRuntime__set_gc_threshold__Int32( RogueInt32 value_0 )
{
  if (value_0 <= 0)
  {
    value_0 = ((RogueInt32)2147483647);
  }
  Rogue_gc_threshold = value_0;

}

RogueString* Rogueget_platform__call()
{
  ROGUE_DEF_LOCAL_REF(RogueString*,target_0,(Rogue_literal_strings[43]));
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_632_2,(RogueSystem_command_line_arguments));
    RogueInt32 _auto_633_3 = (0);
    for (;_auto_633_3 < _auto_632_2->count;++_auto_633_3)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,arg_4,(((RogueString*)(_auto_632_2->data->as_objects[_auto_633_3]))));
      {
        if ((RogueString__operatorEQUALSEQUALS__String_String( arg_4, Rogue_literal_strings[44] )))
        {
          ((RogueClassBuildConfig*)ROGUE_SINGLETON(BuildConfig))->ide_flag = true;
        }
        else
        {
          target_0 = ((RogueString*)arg_4);
        }
      }
    }
  }
  ROGUE_TRY
  {
    {
      if ((((((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[19] ))) || ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[18] ))))) || ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[34] )))))
      {
      }
      else if ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[36] )))
      {
        if ((RogueString__operatorEQUALSEQUALS__String_String( ROGUE_ARG((RogueSystem__os())), Rogue_literal_strings[18] )))
        {
          Rogueinstall_emscripten__call();
        }
      }
      else
      {
        RogueGlobal__println__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), Rogue_literal_strings[69] );
        RogueSystem__exit__Int32( 1 );
      }
    }
  }
  ROGUE_CATCH( RogueClassError,err_1 )
  {
    RogueGlobal__println__Object( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), ROGUE_ARG(((RogueObject*)(err_1))) );
    RogueSystem__exit__Int32( 1 );
  }
  ROGUE_END_TRY
  return (RogueString*)(target_0);
}

void Roguestandard_build__call__String( RogueString* target_0 )
{
  ROGUE_TRY
  {
    Rogueconfigure_build_folder__call__String( target_0 );
    Roguecompile__call__String( target_0 );
  }
  ROGUE_CATCH( RogueClassError,err_1 )
  {
    RogueGlobal__println__Object( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), ROGUE_ARG(((RogueObject*)(err_1))) );
    RogueSystem__exit__Int32( 1 );
  }
  ROGUE_END_TRY
}

void RogueSystem__exit__Int32( RogueInt32 result_code_0 )
{
  Rogue_quit();
  exit( result_code_0 );

}

RogueString* RogueSystem__os()
{
  ROGUE_DEF_LOCAL_REF(RogueString*,result_0,(Rogue_literal_strings[34]));
#if __APPLE__
    #if TARGET_IPHONE_SIMULATOR || TARGET_OS_IPHONE

  result_0 = ((RogueString*)Rogue_literal_strings[19]);
    #else

  result_0 = ((RogueString*)Rogue_literal_strings[18]);
    #endif
#elif _WIN64 || _WIN32

  result_0 = ((RogueString*)Rogue_literal_strings[33]);
#elif ANDROID

  result_0 = ((RogueString*)Rogue_literal_strings[45]);
#elif __CYGWIN__

  result_0 = ((RogueString*)Rogue_literal_strings[46]);
#elif defined(EMSCRIPTEN)

  result_0 = ((RogueString*)Rogue_literal_strings[36]);
#endif

  return (RogueString*)(result_0);
}

RogueInt32 RogueSystem__run__String( RogueString* command_0 )
{
  RogueInt32 return_val_1 = (0);
  return_val_1 = system( (char*)command_0->utf8 );

  if (return_val_1 == -1)
  {
    ROGUE_THROW(RogueClassError,((RogueClassError*)((Rogue_call_ROGUEM16( 17, ROGUE_ARG(((RogueException*)ROGUE_CREATE_REF(RogueClassError*,ROGUE_CREATE_OBJECT(Error)))), Rogue_literal_strings[42] )))));
  }
  return (RogueInt32)(return_val_1);
}

void RogueSystem__init_class()
{
  RogueSystem_command_line_arguments = ((RogueString_List__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueString_List*,ROGUE_CREATE_OBJECT(String_List))) )));
}

RogueString* RogueFile__absolute_filepath__String( RogueString* filepath_0 )
{
  if (!(!!(filepath_0)))
  {
    return (RogueString*)(((RogueString*)(NULL)));
  }
  if (!((RogueFile__exists__String( filepath_0 ))))
  {
    ROGUE_DEF_LOCAL_REF(RogueString*,parent_1,((RogueFile__folder__String( filepath_0 ))));
    if (parent_1->character_count == 0)
    {
      parent_1 = ((RogueString*)Rogue_literal_strings[4]);
    }
    return (RogueString*)(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG((RogueFile__absolute_filepath__String( parent_1 ))) ))) )))), Rogue_literal_strings[5] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG((RogueFile__filename__String( filepath_0 ))) ))) )))) ))));
  }
  ROGUE_DEF_LOCAL_REF(RogueString*,return_value_2,0);
#if defined(_WIN32)
  {
    char long_name[PATH_MAX+4];
    char full_name[PATH_MAX+4];
    if (GetInt64PathName((char*)filepath_0->utf8, long_name, PATH_MAX+4) == 0)
    {
      strcpy_s( long_name, PATH_MAX+4, (char*)filepath_0->utf8 );
    }
    if (GetFullPathName(long_name, PATH_MAX+4, full_name, 0) != 0)
    {
      return_value_2 = RogueString_create_from_utf8( full_name, -1 );
    }
  }
#else
  {
    int original_dir_fd;
    int new_dir_fd;
    char filename[PATH_MAX];
    char c_filepath[ PATH_MAX ];
    bool is_folder;
    is_folder = RogueFile__is_folder__String( filepath_0 );
    int len = filepath_0->byte_count;
    if (len >= PATH_MAX) len = PATH_MAX - 1;
    memcpy( c_filepath, (char*)filepath_0->utf8, len );
    c_filepath[len] = 0;
    // A way to get back to the starting folder when finished.
    original_dir_fd = open( ".", O_RDONLY );
    if (is_folder)
    {
      filename[0] = 0;
    }
    else
    {
      // fchdir only works with a path, not a path+filename (c_filepath).
      // Copy out the filename and null terminate the filepath to be just a path.
      int i = (int) strlen( c_filepath ) - 1;
      while (i >= 0 && c_filepath[i] != '/') --i;
      strcpy( filename, c_filepath+i+1 );
      if (i == -1) strcpy( c_filepath, "." );
      else         c_filepath[i] = 0;
    }
    new_dir_fd = open( c_filepath, O_RDONLY );
    do
    {
      if (original_dir_fd >= 0 && new_dir_fd >= 0)
      {
        int r = fchdir( new_dir_fd );
        if ( r != 0 ) break;
        char * r2 = getcwd( c_filepath, PATH_MAX );
        if ( r2 == 0 ) break;
        if ( !is_folder )
        {
          strcat( c_filepath, "/" );
          strcat( c_filepath, filename );
        }
        r = fchdir( original_dir_fd );
        if ( r != 0 ) break;
      }
      return_value_2 = RogueString_create_from_utf8( c_filepath, -1 );
    } while (false);
    if (original_dir_fd >= 0) close( original_dir_fd );
    if (new_dir_fd >= 0) close( new_dir_fd );
  }
#endif

  if (((void*)return_value_2) == ((void*)NULL))
  {
    ROGUE_THROW(RogueClassIOError,((RogueClassIOError*)((Rogue_call_ROGUEM16( 17, ROGUE_ARG(((RogueException*)ROGUE_CREATE_REF(RogueClassIOError*,ROGUE_CREATE_OBJECT(IOError)))), Rogue_literal_strings[16] )))));
  }
  return (RogueString*)(return_value_2);
}

RogueLogical RogueFile__create_folder__String( RogueString* _auto_941 )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,filepath_0,_auto_941);
  filepath_0 = ((RogueString*)(RogueFile__absolute_filepath__String( filepath_0 )));
  if ((RogueFile__exists__String( filepath_0 )))
  {
    return (RogueLogical)((RogueFile__is_folder__String( filepath_0 )));
  }
  ROGUE_DEF_LOCAL_REF(RogueString*,parent_1,((RogueFile__folder__String( filepath_0 ))));
  if (!((RogueFile__create_folder__String( parent_1 ))))
  {
    return (RogueLogical)(false);
  }
  return (0 == mkdir((char*)filepath_0->utf8, 0777));

}

RogueLogical RogueFile__exists__String( RogueString* filepath_0 )
{
  if ( !filepath_0 ) return false;
  FILE* fp = fopen( (char*)filepath_0->utf8, "rb" );
  if ( !fp ) return false;
  fclose( fp );
  return true;

}

RogueString* RogueFile__filename__String( RogueString* filepath_0 )
{
  RogueOptionalInt32 i_1 = (((RogueString__locate_last__Character_OptionalInt32( filepath_0, (RogueCharacter)'/', ROGUE_ARG((RogueOptionalInt32__create())) ))));
  if (!(i_1.exists))
  {
    i_1 = ((RogueOptionalInt32)((RogueString__locate_last__Character_OptionalInt32( filepath_0, (RogueCharacter)'\\', ROGUE_ARG((RogueOptionalInt32__create())) ))));
  }
  if (!(i_1.exists))
  {
    return (RogueString*)(filepath_0);
  }
  return (RogueString*)(((RogueString__from__Int32( filepath_0, ROGUE_ARG(((i_1.value) + (1))) ))));
}

RogueString* RogueFile__folder__String( RogueString* filepath_0 )
{
  RogueOptionalInt32 i_1 = (((RogueString__locate_last__Character_OptionalInt32( filepath_0, (RogueCharacter)'/', ROGUE_ARG((RogueOptionalInt32__create())) ))));
  if (!(i_1.exists))
  {
    i_1 = ((RogueOptionalInt32)((RogueString__locate_last__Character_OptionalInt32( filepath_0, (RogueCharacter)'\\', ROGUE_ARG((RogueOptionalInt32__create())) ))));
  }
  if (!(i_1.exists))
  {
    return (RogueString*)(Rogue_literal_strings[0]);
  }
  return (RogueString*)(((RogueString__from__Int32_Int32( filepath_0, 0, ROGUE_ARG(((i_1.value) - (1))) ))));
}

RogueLogical RogueFile__is_folder__String( RogueString* filepath_0 )
{
  if ( !filepath_0 ) return false;
#if defined(_WIN32)
    char filepath_copy[PATH_MAX];
    strcpy( filepath_copy, (char*)filepath_0->utf8 );
    int path_len = filepath_0->byte_count;
    int i = strlen(filepath_copy)-1;
    while (i > 0 && (filepath_copy[i] == '/' || filepath_copy[i] == '\\')) filepath_copy[i--] = 0;
    // Windows allows dir\* to count as a directory; guard against.
    for (i=0; filepath_copy[i]; ++i)
    {
      if (filepath_copy[i] == '*' || filepath_copy[i] == '?') return 0;
    }
    WIN32_FIND_DATA entry;
    HANDLE dir = FindFirstFile( filepath_copy, &entry );
    if (dir != INVALID_HANDLE_VALUE)
    {
      if (entry.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)
      {
        FindClose( dir );
        return 1;
      }
    }
    FindClose( dir );
    return 0;
#else
    DIR* dir = opendir( (char*)filepath_0->utf8 );
    if ( !dir ) return 0;
    closedir( dir );
    return 1;
#endif

}

RogueString_List* RogueFile__listing__String_Logical_Logical_Logical_Logical( RogueString* folder_0, RogueLogical ignore_hidden_1, RogueLogical recursive_2, RogueLogical absolute_3, RogueLogical omit_path_4 )
{
  RogueClassFileOptions options_5 = (RogueClassFileOptions( 0 ));
  if (ignore_hidden_1)
  {
    options_5 = ((RogueClassFileOptions)RogueClassFileOptions( ((options_5.flags) | (32)) ));
  }
  if (recursive_2)
  {
    options_5 = ((RogueClassFileOptions)RogueClassFileOptions( ((options_5.flags) | (1)) ));
  }
  if (absolute_3)
  {
    options_5 = ((RogueClassFileOptions)RogueClassFileOptions( ((options_5.flags) | (4)) ));
  }
  if (omit_path_4)
  {
    options_5 = ((RogueClassFileOptions)RogueClassFileOptions( ((options_5.flags) | (2)) ));
  }
  return (RogueString_List*)((RogueFile__listing__String_FileOptions( folder_0, options_5 )));
}

RogueString_List* RogueFile__listing__String_FileOptions( RogueString* folder_0, RogueClassFileOptions options_1 )
{
  if (((((RogueString__contains__Character( folder_0, (RogueCharacter)'*' )))) || (((RogueString__contains__Character( folder_0, (RogueCharacter)'?' ))))))
  {
    ROGUE_DEF_LOCAL_REF(RogueString*,full_pattern_2,(folder_0));
    ROGUE_DEF_LOCAL_REF(RogueString_List*,parts_3,(((RogueString__split__Character( ROGUE_ARG(((RogueString__replacing__Character_Character( folder_0, (RogueCharacter)'\\', (RogueCharacter)'/' )))), (RogueCharacter)'/' )))));
    ROGUE_DEF_LOCAL_REF(RogueString_List*,non_wild_parts_4,(((RogueString_List__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueString_List*,ROGUE_CREATE_OBJECT(String_List))) )))));
    while (((!(((RogueString__contains__Character( ROGUE_ARG(((RogueString*)(parts_3->data->as_objects[0]))), (RogueCharacter)'*' ))))) && (!(((RogueString__contains__Character( ROGUE_ARG(((RogueString*)(parts_3->data->as_objects[0]))), (RogueCharacter)'?' )))))))
    {
      RogueString_List__add__String( non_wild_parts_4, ROGUE_ARG(((RogueString_List__remove_at__Int32( parts_3, 0 )))) );
    }
    ROGUE_DEF_LOCAL_REF(RogueString*,non_wild_path_5,(((((non_wild_parts_4->count))) ? (ROGUE_ARG(((RogueString_List__join__String( non_wild_parts_4, ROGUE_ARG(((RogueCharacter__to_String( (RogueCharacter)'/' )))) ))))) : ROGUE_ARG(Rogue_literal_strings[4]))));
    if (((RogueString__contains__String( ROGUE_ARG(((RogueString*)(parts_3->data->as_objects[0]))), Rogue_literal_strings[23] ))))
    {
      ROGUE_DEF_LOCAL_REF(RogueString_List*,filtered_6,(((RogueString_List__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueString_List*,ROGUE_CREATE_OBJECT(String_List))) )))));
      {
        ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_689_10,((RogueFile__listing__String_FileOptions( non_wild_path_5, ROGUE_ARG(RogueClassFileOptions( ((RogueClassFileOptions( ((options_1.flags) | (1)) ).flags) & (-3)) )) ))));
        RogueInt32 _auto_690_11 = (0);
        for (;_auto_690_11 < _auto_689_10->count;++_auto_690_11)
        {
          ROGUE_DEF_LOCAL_REF(RogueString*,filepath_12,(((RogueString*)(_auto_689_10->data->as_objects[_auto_690_11]))));
          if ((RogueFile__matches_wildcard_pattern__String_String( filepath_12, full_pattern_2 )))
          {
            if (!!(((options_1.flags) & (2))))
            {
              RogueString_List__add__String( filtered_6, ROGUE_ARG(((RogueString__after_first__String( filepath_12, folder_0 )))) );
            }
            else if (!!(((options_1.flags) & (4))))
            {
              RogueString_List__add__String( filtered_6, ROGUE_ARG((RogueFile__absolute_filepath__String( filepath_12 ))) );
            }
            else
            {
              RogueString_List__add__String( filtered_6, filepath_12 );
            }
          }
        }
      }
      return (RogueString_List*)(filtered_6);
    }
    else
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,pattern_7,(((RogueString_List__remove_at__Int32( parts_3, 0 )))));
      ROGUE_DEF_LOCAL_REF(RogueString_List*,results_8,(((RogueString_List__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueString_List*,ROGUE_CREATE_OBJECT(String_List))) )))));
      {
        ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_691_13,((RogueFile__listing__String_FileOptions( non_wild_path_5, ROGUE_ARG(RogueClassFileOptions( ((RogueClassFileOptions( ((options_1.flags) & (-2)) ).flags) | (2)) )) ))));
        RogueInt32 _auto_692_14 = (0);
        for (;_auto_692_14 < _auto_691_13->count;++_auto_692_14)
        {
          ROGUE_DEF_LOCAL_REF(RogueString*,name_15,(((RogueString*)(_auto_691_13->data->as_objects[_auto_692_14]))));
          if (((RogueString__begins_with__Character( name_15, (RogueCharacter)'.' ))))
          {
            continue;
          }
          if ((RogueFile__matches_wildcard_pattern__String_String( name_15, pattern_7 )))
          {
            if ((RogueString__operatorEQUALSEQUALS__String_String( non_wild_path_5, Rogue_literal_strings[4] )))
            {
              if ((RogueFile__is_folder__String( name_15 )))
              {
                if (!!(parts_3->count))
                {
                  RogueString_List__add__String_List( results_8, ROGUE_ARG((RogueFile__listing__String_FileOptions( ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], name_15 ))) )))), Rogue_literal_strings[5] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG(((RogueString_List__join__String( parts_3, ROGUE_ARG(((RogueCharacter__to_String( (RogueCharacter)'/' )))) )))) ))) )))) )))), options_1 ))) );
                }
                else if (!!(((options_1.flags) & (1))))
                {
                  RogueString_List__add__String_List( results_8, ROGUE_ARG((RogueFile__listing__String_FileOptions( ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], name_15 ))) )))) )))), options_1 ))) );
                }
                else
                {
                  RogueString_List__add__String( results_8, name_15 );
                }
              }
              else if (((RogueString_List__is_empty( parts_3 ))))
              {
                RogueString_List__add__String( results_8, name_15 );
              }
            }
            else
            {
              ROGUE_DEF_LOCAL_REF(RogueString*,subfolder_9,(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], non_wild_path_5 ))) )))), Rogue_literal_strings[5] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], name_15 ))) )))) )))));
              if ((RogueFile__is_folder__String( subfolder_9 )))
              {
                if (!!(parts_3->count))
                {
                  RogueString_List__add__String_List( results_8, ROGUE_ARG((RogueFile__listing__String_FileOptions( ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], subfolder_9 ))) )))), Rogue_literal_strings[5] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG(((RogueString_List__join__String( parts_3, ROGUE_ARG(((RogueCharacter__to_String( (RogueCharacter)'/' )))) )))) ))) )))) )))), options_1 ))) );
                }
                else if (!!(((options_1.flags) & (1))))
                {
                  RogueString_List__add__String_List( results_8, ROGUE_ARG((RogueFile__listing__String_FileOptions( subfolder_9, options_1 ))) );
                }
                else
                {
                  RogueString_List__add__String( results_8, subfolder_9 );
                }
              }
              else if (((RogueString_List__is_empty( parts_3 ))))
              {
                RogueString_List__add__String( results_8, subfolder_9 );
              }
            }
          }
        }
      }
      return (RogueString_List*)(results_8);
    }
  }
  else
  {
    return (RogueString_List*)((RogueFile__listing__String_FileOptions_String_String_List( folder_0, options_1, Rogue_literal_strings[0], ROGUE_ARG(((RogueString_List__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueString_List*,ROGUE_CREATE_OBJECT(String_List))) )))) )));
  }
}

RogueString_List* RogueFile__listing__String_FileOptions_String_String_List( RogueString* _auto_942, RogueClassFileOptions options_1, RogueString* _auto_943, RogueString_List* result_3 )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,folder_0,_auto_942);
  ROGUE_DEF_LOCAL_REF(RogueString*,filepath_2,_auto_943);
  if ((RogueString__operatorEQUALSEQUALS__String_String( folder_0, Rogue_literal_strings[4] )))
  {
    options_1 = ((RogueClassFileOptions)RogueClassFileOptions( ((options_1.flags) | (2)) ));
  }
  if (!(!!(((options_1.flags) & (2)))))
  {
    if (!!(((options_1.flags) & (4))))
    {
      filepath_2 = ((RogueString*)(RogueFile__absolute_filepath__String( folder_0 )));
      folder_0 = ((RogueString*)Rogue_literal_strings[0]);
      options_1 = ((RogueClassFileOptions)RogueClassFileOptions( ((options_1.flags) | (2)) ));
    }
    else
    {
      filepath_2 = ((RogueString*)folder_0);
      folder_0 = ((RogueString*)Rogue_literal_strings[0]);
      options_1 = ((RogueClassFileOptions)RogueClassFileOptions( ((options_1.flags) | (2)) ));
    }
  }
  if (((!!(folder_0->character_count)) && (!(((((RogueString__ends_with__Character( folder_0, (RogueCharacter)'/' )))) || (((RogueString__ends_with__Character( folder_0, (RogueCharacter)'\\' )))))))))
  {
    folder_0 = ((RogueString*)((RogueString__operatorPLUS__Character( folder_0, (RogueCharacter)'/' ))));
  }
  ROGUE_DEF_LOCAL_REF(RogueString*,native_folder_4,((RogueString__operatorPLUS__String_String( folder_0, filepath_2 ))));
  if (!((RogueFile__is_folder__String( native_folder_4 ))))
  {
    if ((RogueFile__exists__String( native_folder_4 )))
    {
      RogueLogical is_hidden_5 = (((RogueString__begins_with__Character( native_folder_4, (RogueCharacter)'.' ))));
      if (!(((is_hidden_5) && (!!(((options_1.flags) & (32)))))))
      {
        if (((RogueFileOptions__is_files( options_1 ))))
        {
          if (((native_folder_4->character_count > 1) && (((RogueString__ends_with__Character( native_folder_4, (RogueCharacter)'/' ))))))
          {
            native_folder_4 = ((RogueString*)((RogueString__leftmost__Int32( native_folder_4, -1 ))));
          }
          RogueString_List__add__String( result_3, native_folder_4 );
        }
      }
    }
    return (RogueString_List*)(result_3);
  }
  if (((!!(filepath_2->character_count)) && (!(((((RogueString__ends_with__Character( filepath_2, (RogueCharacter)'/' )))) || (((RogueString__ends_with__Character( filepath_2, (RogueCharacter)'\\' )))))))))
  {
    filepath_2 = ((RogueString*)((RogueString__operatorPLUS__Character( filepath_2, (RogueCharacter)'/' ))));
  }
  {
    DIR* dir;
    struct dirent* entry;
    dir = opendir( (const char*) native_folder_4->utf8 );
    if (dir)
    {
      entry = readdir( dir );
      while (entry)
      {
        int keep = 1;
        if (entry->d_name[0] == '.')
        {
          switch (entry->d_name[1])
          {
            case 0:
              keep = 0;
              break;
            case '.':
              keep = entry->d_name[2] != 0;
              break;
          }
        }
        if (keep)
        {

  ROGUE_DEF_LOCAL_REF(RogueString*,entry_6,(RogueString_create_from_utf8(entry->d_name,-1)));
  RogueLogical is_hidden_7 = (((RogueString__begins_with__Character( entry_6, (RogueCharacter)'.' ))));
  entry_6 = ((RogueString*)(RogueString__operatorPLUS__String_String( filepath_2, entry_6 )));
  if (!(((is_hidden_7) && (!!(((options_1.flags) & (32)))))))
  {
    RogueLogical _is_folder_8 = ((RogueFile__is_folder__String( ROGUE_ARG((RogueString__operatorPLUS__String_String( folder_0, entry_6 ))) )));
    if (((((((RogueFileOptions__is_files_and_folders( options_1 )))) || (((_is_folder_8) && (((RogueFileOptions__is_folders( options_1 )))))))) || (((!(_is_folder_8)) && (((RogueFileOptions__is_files( options_1 ))))))))
    {
      RogueString_List__add__String( result_3, entry_6 );
    }
    if (((((_is_folder_8) && (!!(((options_1.flags) & (1)))))) && (!!(entry_6->character_count))))
    {
      RogueFile__listing__String_FileOptions_String_String_List( folder_0, options_1, entry_6, result_3 );
    }
  }
        }
        entry = readdir( dir );
      }
      closedir( dir );
    }
  }

  return (RogueString_List*)(result_3);
}

RogueLogical RogueFile__matches_wildcard_pattern__String_String( RogueString* filepath_0, RogueString* pattern_1 )
{
  RogueInt32 c_2 = (filepath_0->character_count);
  if (pattern_1->character_count == 0)
  {
    return (RogueLogical)(c_2 == 0);
  }
  ROGUE_DEF_LOCAL_REF(RogueString*,remaining_pattern_3,(((RogueString__from__Int32( pattern_1, 1 )))));
  RogueCharacter ch_4 = (RogueString_character_at(pattern_1,0));
  switch (ch_4)
  {
    case (RogueCharacter)'*':
    {
      if (((!!(remaining_pattern_3->character_count)) && (RogueString_character_at(remaining_pattern_3,0) == (RogueCharacter)'*')))
      {
        remaining_pattern_3 = ((RogueString*)((RogueString__from__Int32( remaining_pattern_3, 1 ))));
        {
          RogueInt32 n_5 = (0);
          RogueInt32 _auto_371_6 = (c_2);
          for (;n_5 <= _auto_371_6;++n_5)
          {
            if ((RogueFile__matches_wildcard_pattern__String_String( ROGUE_ARG(((RogueString__from__Int32( filepath_0, n_5 )))), remaining_pattern_3 )))
            {
              return (RogueLogical)(true);
            }
          }
        }
      }
      else
      {
        {
          RogueInt32 n_7 = (0);
          RogueInt32 _auto_372_8 = (c_2);
          for (;n_7 < _auto_372_8;++n_7)
          {
            ch_4 = ((RogueCharacter)RogueString_character_at(filepath_0,n_7));
            if ((RogueFile__matches_wildcard_pattern__String_String( ROGUE_ARG(((RogueString__from__Int32( filepath_0, n_7 )))), remaining_pattern_3 )))
            {
              return (RogueLogical)(true);
            }
            if (((ch_4 == (RogueCharacter)'/') || (ch_4 == (RogueCharacter)'\\')))
            {
              return (RogueLogical)(false);
            }
          }
        }
        return (RogueLogical)((RogueFile__matches_wildcard_pattern__String_String( Rogue_literal_strings[0], remaining_pattern_3 )));
      }
      break;
    }
    case (RogueCharacter)'?':
    {
      if (c_2 == 0)
      {
        return (RogueLogical)(false);
      }
      ch_4 = ((RogueCharacter)RogueString_character_at(filepath_0,0));
      if (((ch_4 == (RogueCharacter)'/') || (ch_4 == (RogueCharacter)'\\')))
      {
        return (RogueLogical)(false);
      }
      return (RogueLogical)((RogueFile__matches_wildcard_pattern__String_String( ROGUE_ARG(((RogueString__from__Int32( filepath_0, 1 )))), remaining_pattern_3 )));
      break;
    }
    default:
    {
      if (c_2 == 0)
      {
        return (RogueLogical)(false);
      }
      if (ch_4 == RogueString_character_at(filepath_0,0))
      {
        return (RogueLogical)((RogueFile__matches_wildcard_pattern__String_String( ROGUE_ARG(((RogueString__from__Int32( filepath_0, 1 )))), remaining_pattern_3 )));
      }
    }
  }
  return (RogueLogical)(false);
}

RogueReal64 RogueFile__timestamp__String( RogueString* filepath_0 )
{
#if defined(_WIN32)
    HANDLE handle = CreateFile( (const char*)filepath_0->utf8, 0, 0, NULL, OPEN_EXISTING,
        FILE_ATTRIBUTE_NORMAL, NULL );
    if (handle != INVALID_HANDLE_VALUE)
    {
      BY_HANDLE_FILE_INFORMATION info;
      if (GetFileInformationByHandle( handle, &info ))
      {
        RogueInt64 result = info.ftLastWriteTime.dwHighDateTime;
        result <<= 32;
        result |= info.ftLastWriteTime.dwLowDateTime;
        result /= 10000; // convert from Crazyseconds to Milliseconds
        result -= 11644473600000;  // base on Jan 1, 1970 instead of Jan 1, 1601 (?!)
        CloseHandle(handle);
        return result / 1000.0;
      }
      CloseHandle(handle);
    }
#elif defined(ROGUE_PLATFORM_UNIX_COMPATIBLE)
    int file_id = open( (const char*)filepath_0->utf8, O_RDONLY );
    if (file_id >= 0)
    {
      struct stat info;
      if (0 == fstat(file_id, &info))
      {
#if defined(__APPLE__)
        RogueInt64 result = info.st_mtimespec.tv_sec;
        result *= 1000000000;
        result += info.st_mtimespec.tv_nsec;
        result /= 1000000;  // convert to milliseconds
#else
        RogueInt64 result = (RogueInt64) info.st_mtime;
        result *= 1000;  // convert to ms
#endif
        close(file_id);
        return result / 1000.0;
      }
      close(file_id);
    }
#else
# error Must define File.timestamp() for this OS.
#endif
  return 0.0;

}

void Rogueinstall_emscripten__call()
{
  Rogueinstall_brew__call();
  Rogueinstall_library__call__String( Rogue_literal_strings[36] );
}

void Rogueconfigure_build_folder__call__String( RogueString* target_0 )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,output_folder_1,(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), Rogue_literal_strings[2] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], target_0 ))) )))), Rogue_literal_strings[3] )))) )))));
  RogueFile__create_folder__String( output_folder_1 );
}

void Roguecompile__call__String( RogueString* target_0 )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,output_folder_1,(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), Rogue_literal_strings[2] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], target_0 ))) )))), Rogue_literal_strings[3] )))) )))));
  if (!((Rogueneed_compile__call__String_String( target_0, output_folder_1 ))))
  {
    return;
  }
  ROGUE_DEF_LOCAL_REF(RogueString*,language_2,(Rogue_literal_strings[29]));
  if ((((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[18] ))) || ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[19] )))))
  {
    language_2 = ((RogueString*)Rogue_literal_strings[30]);
  }
  ROGUE_DEF_LOCAL_REF(RogueString*,exe_3,(Rogue_literal_strings[31]));
#ifdef ROGUEC
    #define MAKE_MACRO_STR(s) MAKE_ARG_STR(s)
    #define MAKE_ARG_STR(s) #s
    exe_3 = RogueString_create_from_utf8(MAKE_MACRO_STR(ROGUEC));
    #undef MAKE_ARG_STR
    #undef MAKE_MACRO_STR
#endif

  ROGUE_DEF_LOCAL_REF(RogueString*,cmd_4,(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], exe_3 ))) )))), Rogue_literal_strings[32] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], language_2 ))) )))), Rogue_literal_strings[8] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], target_0 ))) )))), Rogue_literal_strings[8] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG((Roguemobile_or_desktop__call__String( target_0 ))) ))) )))), Rogue_literal_strings[39] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], output_folder_1 ))) )))), Rogue_literal_strings[40] )))) )))));
  if (((RogueClassBuildConfig*)ROGUE_SINGLETON(BuildConfig))->ide_flag)
  {
    cmd_4 = ((RogueString*)((RogueString__operatorPLUS__String( cmd_4, Rogue_literal_strings[41] ))));
  }
  RogueGlobal__println__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), cmd_4 );
  if (!!((RogueSystem__run__String( cmd_4 ))))
  {
    RogueSystem__exit__Int32( 1 );
  }
}

void Rogueinstall_brew__call()
{
  if (0 == (RogueSystem__run__String( Rogue_literal_strings[47] )))
  {
    return;
  }
  Roguerequire_command_line__call();
  RogueGlobal__println__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), Rogue_literal_strings[55] );
  if (((RogueString__begins_with__Character( ROGUE_ARG(((RogueString__to_lowercase( ROGUE_ARG((RogueConsole__input__String( Rogue_literal_strings[56] ))) )))), (RogueCharacter)'y' ))))
  {
    ROGUE_DEF_LOCAL_REF(RogueString*,cmd_0,(Rogue_literal_strings[57]));
    RogueGlobal__println__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), cmd_0 );
    if (0 == (RogueSystem__run__String( cmd_0 )))
    {
      return;
    }
    ROGUE_THROW(RogueClassError,((RogueClassError*)((Rogue_call_ROGUEM16( 17, ROGUE_ARG(((RogueException*)ROGUE_CREATE_REF(RogueClassError*,ROGUE_CREATE_OBJECT(Error)))), Rogue_literal_strings[58] )))));
  }
  ROGUE_THROW(RogueClassError,((RogueClassError*)((Rogue_call_ROGUEM16( 17, ROGUE_ARG(((RogueException*)ROGUE_CREATE_REF(RogueClassError*,ROGUE_CREATE_OBJECT(Error)))), Rogue_literal_strings[59] )))));
}

void Rogueinstall_library__call__String( RogueString* library_name_0 )
{
  if (0 == (RogueSystem__run__String( ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), Rogue_literal_strings[60] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], library_name_0 ))) )))), Rogue_literal_strings[61] )))) )))) )))
  {
    return;
  }
  Roguerequire_command_line__call();
  if (!(((RogueString__begins_with__Character( ROGUE_ARG(((RogueString__to_lowercase( ROGUE_ARG((RogueConsole__input__String( ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), Rogue_literal_strings[62] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], library_name_0 ))) )))), Rogue_literal_strings[63] )))) )))) ))) )))), (RogueCharacter)'y' )))))
  {
    ROGUE_THROW(RogueClassError,((RogueClassError*)((Rogue_call_ROGUEM16( 17, ROGUE_ARG(((RogueException*)ROGUE_CREATE_REF(RogueClassError*,ROGUE_CREATE_OBJECT(Error)))), ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), Rogue_literal_strings[64] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], library_name_0 ))) )))), Rogue_literal_strings[65] )))) )))) )))));
  }
  ROGUE_DEF_LOCAL_REF(RogueString*,cmd_1,(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), Rogue_literal_strings[66] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], library_name_0 ))) )))) )))));
  RogueGlobal__println__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), cmd_1 );
  if (0 != (RogueSystem__run__String( cmd_1 )))
  {
    ROGUE_THROW(RogueClassError,((RogueClassError*)((Rogue_call_ROGUEM16( 17, ROGUE_ARG(((RogueException*)ROGUE_CREATE_REF(RogueClassError*,ROGUE_CREATE_OBJECT(Error)))), ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), Rogue_literal_strings[67] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], library_name_0 ))) )))), Rogue_literal_strings[65] )))) )))) )))));
  }
  if ((RogueString__operatorEQUALSEQUALS__String_String( library_name_0, Rogue_literal_strings[36] )))
  {
    RogueGlobal__println__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), ROGUE_ARG((RogueString__operatorTIMES__String_Int32( Rogue_literal_strings[7], 79 ))) );
    RogueGlobal__println__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), Rogue_literal_strings[68] );
    RogueGlobal__println__String( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), ROGUE_ARG((RogueString__operatorTIMES__String_Int32( Rogue_literal_strings[7], 79 ))) );
    RogueSystem__exit__Int32( 1 );
  }
}

RogueLogical Rogueneed_compile__call__String_String( RogueString* target_0, RogueString* output_folder_1 )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,extension_2,(Rogue_literal_strings[17]));
  if ((((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[18] ))) || ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[19] )))))
  {
    extension_2 = ((RogueString*)Rogue_literal_strings[20]);
  }
  ROGUE_DEF_LOCAL_REF(RogueString*,output_h_3,(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], output_folder_1 ))) )))), Rogue_literal_strings[21] )))) )))));
  ROGUE_DEF_LOCAL_REF(RogueString*,output_cpp_4,(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], output_folder_1 ))) )))), Rogue_literal_strings[22] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], extension_2 ))) )))) )))));
  if (!((RogueFile__exists__String( output_h_3 ))))
  {
    return (RogueLogical)(true);
  }
  if (!((RogueFile__exists__String( output_cpp_4 ))))
  {
    return (RogueLogical)(true);
  }
  ROGUE_DEF_LOCAL_REF(RogueString_List*,dependencies_5,((RogueFile__listing__String_Logical_Logical_Logical_Logical( Rogue_literal_strings[24], false, true, true, false ))));
  RogueString_List__add__String_List( dependencies_5, ROGUE_ARG((RogueFile__listing__String_Logical_Logical_Logical_Logical( Rogue_literal_strings[25], false, true, true, false ))) );
  RogueString_List__add__String( dependencies_5, Rogue_literal_strings[26] );
  RogueString_List__add__String( dependencies_5, Rogue_literal_strings[27] );
  RogueString_List__add__String( dependencies_5, Rogue_literal_strings[28] );
  RogueReal64 timestamp_6 = (((RogueReal64__or_smaller__Real64( ROGUE_ARG((RogueFile__timestamp__String( output_h_3 ))), ROGUE_ARG((RogueFile__timestamp__String( output_cpp_4 ))) ))));
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_930_7,(dependencies_5));
    RogueInt32 _auto_931_8 = (0);
    for (;_auto_931_8 < _auto_930_7->count;++_auto_931_8)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,dependency_9,(((RogueString*)(_auto_930_7->data->as_objects[_auto_931_8]))));
      if ((RogueFile__timestamp__String( dependency_9 )) > timestamp_6)
      {
        return (RogueLogical)(true);
      }
    }
  }
  return (RogueLogical)(false);
}

RogueString* Roguemobile_or_desktop__call__String( RogueString* target_0 )
{
  {
    if ((((((((((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[33] ))) || ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[18] ))))) || ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[34] ))))) || ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[35] ))))) || ((RogueString__operatorEQUALSEQUALS__String_String( target_0, Rogue_literal_strings[36] )))))
    {
      return (RogueString*)(Rogue_literal_strings[37]);
    }
    else
    {
      return (RogueString*)(Rogue_literal_strings[38]);
    }
  }
}

void Roguerequire_command_line__call()
{
  if (!!(((RogueSystemEnvironment__get__String( ROGUE_ARG(RogueSystem_environment), Rogue_literal_strings[48] )))))
  {
    ROGUE_DEF_LOCAL_REF(RogueString*,_auto_929_0,(((RogueSystemEnvironment__get__String( ROGUE_ARG(RogueSystem_environment), Rogue_literal_strings[49] )))));
    ROGUE_THROW(RogueClassError,((RogueClassError*)((Rogue_call_ROGUEM16( 17, ROGUE_ARG(((RogueException*)ROGUE_CREATE_REF(RogueClassError*,ROGUE_CREATE_OBJECT(Error)))), ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], Rogue_literal_strings[50] ))) )))), Rogue_literal_strings[51] )))), ROGUE_ARG(((RogueString__operatorPLUS__Int32( ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], Rogue_literal_strings[0] ))), 141 )))) )))), Rogue_literal_strings[53] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG(((RogueString__to_lowercase( ROGUE_ARG(((((_auto_929_0))) ? (ROGUE_ARG(_auto_929_0)) : ROGUE_ARG(Rogue_literal_strings[0]))) )))) ))) )))), Rogue_literal_strings[54] )))) )))) )))));
  }
}

RogueOptionalInt32 RogueOptionalInt32__create()
{
  RogueInt32 default_value_0 = 0;
  return (RogueOptionalInt32)(RogueOptionalInt32( default_value_0, false ));
}


void RogueObject__init_object( RogueObject* THIS )
{
}

RogueObject* RogueObject__init( RogueObject* THIS )
{
  return (RogueObject*)(THIS);
}

RogueInt64 RogueObject__object_id( RogueObject* THIS )
{
  RogueInt64 addr_0 = 0;
  addr_0 = (RogueInt64)(intptr_t)THIS;

  return (RogueInt64)(addr_0);
}

RogueString* RogueObject__to_String( RogueObject* THIS )
{
  return (RogueString*)(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), Rogue_literal_strings[10] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG((Rogue_call_ROGUEM2( 16, ROGUE_ARG(THIS) ))) ))) )))), Rogue_literal_strings[12] )))), ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG(((RogueInt64__to_hex_string__Int32( ROGUE_ARG(((RogueObject__object_id( ROGUE_ARG(THIS) )))), 16 )))) ))) )))), Rogue_literal_strings[13] )))) ))));
}

RogueString* RogueObject__type_name( RogueObject* THIS )
{
  return (RogueString*)(Rogue_literal_strings[11]);
}

RogueClassGlobal* RogueGlobal__init_object( RogueClassGlobal* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  THIS->console = ((RogueClassPrintWriter*)(((RogueClassConsole*)ROGUE_SINGLETON(Console))));
  THIS->global_output_buffer = ((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )));
  return (RogueClassGlobal*)(THIS);
}

RogueClassGlobal* RogueGlobal__init( RogueClassGlobal* THIS )
{
  RogueGlobal__on_exit__Function__( ROGUE_ARG(THIS), ROGUE_ARG(((((RogueClassFunction__*)(((RogueClassFunction_190*)ROGUE_SINGLETON(Function_190))))))) );
  return (RogueClassGlobal*)(THIS);
}

RogueString* RogueGlobal__type_name( RogueClassGlobal* THIS )
{
  return (RogueString*)(Rogue_literal_strings[73]);
}

RogueClassGlobal* RogueGlobal__flush( RogueClassGlobal* THIS )
{
  RogueGlobal__write__StringBuilder( ROGUE_ARG(THIS), ROGUE_ARG(THIS->global_output_buffer) );
  RogueStringBuilder__clear( ROGUE_ARG(THIS->global_output_buffer) );
  return (RogueClassGlobal*)(THIS);
}

RogueClassGlobal* RogueGlobal__print__Object( RogueClassGlobal* THIS, RogueObject* value_0 )
{
  RogueStringBuilder__print__Object( ROGUE_ARG(THIS->global_output_buffer), value_0 );
  return (RogueClassGlobal*)(THIS);
}

RogueClassGlobal* RogueGlobal__print__String( RogueClassGlobal* THIS, RogueString* value_0 )
{
  RogueStringBuilder__print__String( ROGUE_ARG(THIS->global_output_buffer), value_0 );
  if (THIS->global_output_buffer->count > 1024)
  {
    RogueGlobal__flush( ROGUE_ARG(THIS) );
  }
  return (RogueClassGlobal*)(THIS);
}

RogueClassGlobal* RogueGlobal__println( RogueClassGlobal* THIS )
{
  RogueStringBuilder__print__Character_Logical( ROGUE_ARG(THIS->global_output_buffer), (RogueCharacter)10, true );
  return (RogueClassGlobal*)(((RogueGlobal__flush( ROGUE_ARG(THIS) ))));
}

RogueClassGlobal* RogueGlobal__println__Object( RogueClassGlobal* THIS, RogueObject* value_0 )
{
  return (RogueClassGlobal*)(((RogueGlobal__println( ROGUE_ARG(((RogueGlobal__print__Object( ROGUE_ARG(THIS), value_0 )))) ))));
}

RogueClassGlobal* RogueGlobal__println__String( RogueClassGlobal* THIS, RogueString* value_0 )
{
  return (RogueClassGlobal*)(((RogueGlobal__println( ROGUE_ARG(((RogueGlobal__print__String( ROGUE_ARG(THIS), value_0 )))) ))));
}

RogueClassGlobal* RogueGlobal__write__StringBuilder( RogueClassGlobal* THIS, RogueStringBuilder* buffer_0 )
{
  RoguePrintWriter__flush( ROGUE_ARG(((RogueObject*)(RoguePrintWriter__write__StringBuilder( ROGUE_ARG(((RogueObject*)THIS->console)), buffer_0 )))) );
  return (RogueClassGlobal*)(THIS);
}

void RogueGlobal__on_launch( RogueClassGlobal* THIS )
{
  Roguestandard_build__call__String( ROGUE_ARG((Rogueget_platform__call())) );
}

void RogueGlobal__run_tests( RogueClassGlobal* THIS )
{
}

void RogueGlobal__call_exit_functions( RogueClassGlobal* THIS )
{
  ROGUE_DEF_LOCAL_REF(RogueFunction___List*,functions_0,(THIS->exit_functions));
  THIS->exit_functions = ((RogueFunction___List*)(NULL));
  if (!!(functions_0))
  {
    {
      ROGUE_DEF_LOCAL_REF(RogueFunction___List*,_auto_191_1,(functions_0));
      RogueInt32 _auto_192_2 = (0);
      for (;_auto_192_2 < _auto_191_1->count;++_auto_192_2)
      {
        ROGUE_DEF_LOCAL_REF(RogueClassFunction__*,fn_3,(((RogueClassFunction__*)(_auto_191_1->data->as_objects[_auto_192_2]))));
        RogueFunction____call( ((RogueObject*)fn_3) );
      }
    }
  }
}

void RogueGlobal__on_exit__Function__( RogueClassGlobal* THIS, RogueClassFunction__* fn_0 )
{
  if (!(!!(THIS->exit_functions)))
  {
    THIS->exit_functions = ((RogueFunction___List__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueFunction___List*,ROGUE_CREATE_OBJECT(Function___List))) )));
  }
  RogueFunction___List__add__Function__( ROGUE_ARG(THIS->exit_functions), ((fn_0)) );
}

RogueClassPrintWriter_global_output_buffer_* RoguePrintWriter_global_output_buffer___flush( RogueObject* THIS )
{
  switch (THIS->type->index)
  {
    case 1:
      return (RogueClassPrintWriter_global_output_buffer_*)RogueGlobal__flush( (RogueClassGlobal*)THIS );
    default:
      return 0;
  }
}

RogueClassPrintWriter_global_output_buffer_* RoguePrintWriter_global_output_buffer___write__StringBuilder( RogueObject* THIS, RogueStringBuilder* buffer_0 )
{
  switch (THIS->type->index)
  {
    case 1:
      return (RogueClassPrintWriter_global_output_buffer_*)RogueGlobal__write__StringBuilder( (RogueClassGlobal*)THIS, buffer_0 );
    default:
      return 0;
  }
}

RogueClassPrintWriter* RoguePrintWriter__flush( RogueObject* THIS )
{
  switch (THIS->type->index)
  {
    case 1:
      return (RogueClassPrintWriter*)RogueGlobal__flush( (RogueClassGlobal*)THIS );
    case 25:
      return (RogueClassPrintWriter*)RogueConsole__flush( (RogueClassConsole*)THIS );
    case 28:
      return (RogueClassPrintWriter*)RogueConsoleErrorPrinter__flush( (RogueClassConsoleErrorPrinter*)THIS );
    default:
      return 0;
  }
}

RogueClassPrintWriter* RoguePrintWriter__write__StringBuilder( RogueObject* THIS, RogueStringBuilder* buffer_0 )
{
  switch (THIS->type->index)
  {
    case 1:
      return (RogueClassPrintWriter*)RogueGlobal__write__StringBuilder( (RogueClassGlobal*)THIS, buffer_0 );
    case 25:
      return (RogueClassPrintWriter*)RogueConsole__write__StringBuilder( (RogueClassConsole*)THIS, buffer_0 );
    case 28:
      return (RogueClassPrintWriter*)RogueConsoleErrorPrinter__write__StringBuilder( (RogueClassConsoleErrorPrinter*)THIS, buffer_0 );
    default:
      return 0;
  }
}

RogueStringBuilder* RogueStringBuilder__init_object( RogueStringBuilder* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  THIS->at_newline = true;
  return (RogueStringBuilder*)(THIS);
}

RogueStringBuilder* RogueStringBuilder__init( RogueStringBuilder* THIS )
{
  RogueStringBuilder__init__Int32( ROGUE_ARG(THIS), 40 );
  return (RogueStringBuilder*)(THIS);
}

RogueString* RogueStringBuilder__to_String( RogueStringBuilder* THIS )
{
  return (RogueString*)(RogueString_create_from_utf8( (char*)THIS->utf8->data->as_bytes, THIS->utf8->count ));
}

RogueString* RogueStringBuilder__type_name( RogueStringBuilder* THIS )
{
  return (RogueString*)(Rogue_literal_strings[77]);
}

RogueStringBuilder* RogueStringBuilder__init__Int32( RogueStringBuilder* THIS, RogueInt32 initial_capacity_0 )
{
  THIS->utf8 = ((RogueByte_List__init__Int32( ROGUE_ARG(ROGUE_CREATE_REF(RogueByte_List*,ROGUE_CREATE_OBJECT(Byte_List))), initial_capacity_0 )));
  return (RogueStringBuilder*)(THIS);
}

RogueStringBuilder* RogueStringBuilder__clear( RogueStringBuilder* THIS )
{
  RogueByte_List__clear( ROGUE_ARG(THIS->utf8) );
  THIS->count = 0;
  THIS->at_newline = true;
  THIS->cursor_index = 0;
  THIS->cursor_offset = 0;
  return (RogueStringBuilder*)(THIS);
}

RogueLogical RogueStringBuilder__needs_indent( RogueStringBuilder* THIS )
{
  return (RogueLogical)(((THIS->at_newline) && (THIS->indent > 0)));
}

RogueStringBuilder* RogueStringBuilder__print__Character_Logical( RogueStringBuilder* THIS, RogueCharacter value_0, RogueLogical formatted_1 )
{
  if (formatted_1)
  {
    if (value_0 == (RogueCharacter)10)
    {
      THIS->at_newline = true;
    }
    else if (((RogueStringBuilder__needs_indent( ROGUE_ARG(THIS) ))))
    {
      RogueStringBuilder__print_indent( ROGUE_ARG(THIS) );
    }
  }
  ++THIS->count;
  if (((RogueInt32)(value_0)) < 0)
  {
    RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), 0 );
  }
  else if (value_0 <= (RogueCharacter__create__Int32( 127 )))
  {
    RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), ROGUE_ARG(((RogueByte)(value_0))) );
  }
  else if (value_0 <= (RogueCharacter__create__Int32( 2047 )))
  {
    RogueByte_List__add__Byte( ROGUE_ARG(((RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), ROGUE_ARG(((RogueByte)(((192) | (((((RogueInt32)(value_0))) >> (6))))))) )))), ROGUE_ARG(((RogueByte)(((128) | (((((RogueInt32)(value_0))) & (63))))))) );
  }
  else if (value_0 <= (RogueCharacter__create__Int32( 65535 )))
  {
    RogueByte_List__add__Byte( ROGUE_ARG(((RogueByte_List__add__Byte( ROGUE_ARG(((RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), ROGUE_ARG(((RogueByte)(((224) | (((((RogueInt32)(value_0))) >> (12))))))) )))), ROGUE_ARG(((RogueByte)(((128) | (((((((RogueInt32)(value_0))) >> (6))) & (63))))))) )))), ROGUE_ARG(((RogueByte)(((128) | (((((RogueInt32)(value_0))) & (63))))))) );
  }
  else if (value_0 <= (RogueCharacter__create__Int32( 1114111 )))
  {
    RogueByte_List__add__Byte( ROGUE_ARG(((RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), ROGUE_ARG(((RogueByte)(((240) | (((((RogueInt32)(value_0))) >> (18))))))) )))), ROGUE_ARG(((RogueByte)(((128) | (((((((RogueInt32)(value_0))) >> (12))) & (63))))))) );
    RogueByte_List__add__Byte( ROGUE_ARG(((RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), ROGUE_ARG(((RogueByte)(((128) | (((((((RogueInt32)(value_0))) >> (6))) & (63))))))) )))), ROGUE_ARG(((RogueByte)(((128) | (((((RogueInt32)(value_0))) & (63))))))) );
  }
  else
  {
    RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), 63 );
  }
  return (RogueStringBuilder*)(THIS);
}

RogueStringBuilder* RogueStringBuilder__print__Int32( RogueStringBuilder* THIS, RogueInt32 value_0 )
{
  return (RogueStringBuilder*)(((RogueStringBuilder__print__Int64( ROGUE_ARG(THIS), ROGUE_ARG(((RogueInt64)(value_0))) ))));
}

RogueStringBuilder* RogueStringBuilder__print__Int64( RogueStringBuilder* THIS, RogueInt64 value_0 )
{
  if (value_0 == ((1LL) << (63LL)))
  {
    return (RogueStringBuilder*)(((RogueStringBuilder__print__String( ROGUE_ARG(THIS), Rogue_literal_strings[52] ))));
  }
  else if (value_0 < 0LL)
  {
    RogueStringBuilder__print__Character_Logical( ROGUE_ARG(THIS), (RogueCharacter)'-', true );
    return (RogueStringBuilder*)(((RogueStringBuilder__print__Int64( ROGUE_ARG(THIS), ROGUE_ARG((-(value_0))) ))));
  }
  else if (value_0 >= 10LL)
  {
    RogueStringBuilder__print__Int64( ROGUE_ARG(THIS), ROGUE_ARG(((value_0) / (10LL))) );
    return (RogueStringBuilder*)(((RogueStringBuilder__print__Character_Logical( ROGUE_ARG(THIS), ROGUE_ARG(((RogueCharacter)(((48LL) + ((RogueMath__mod__Int64_Int64( value_0, 10LL ))))))), true ))));
  }
  else
  {
    return (RogueStringBuilder*)(((RogueStringBuilder__print__Character_Logical( ROGUE_ARG(THIS), ROGUE_ARG(((RogueCharacter)(((48LL) + (value_0))))), true ))));
  }
}

RogueStringBuilder* RogueStringBuilder__print__Object( RogueStringBuilder* THIS, RogueObject* value_0 )
{
  if (!!(value_0))
  {
    return (RogueStringBuilder*)(((RogueStringBuilder__print__String( ROGUE_ARG(THIS), ROGUE_ARG((Rogue_call_ROGUEM2( 11, value_0 ))) ))));
  }
  return (RogueStringBuilder*)(((RogueStringBuilder__print__String( ROGUE_ARG(THIS), Rogue_literal_strings[1] ))));
}

RogueStringBuilder* RogueStringBuilder__print__String( RogueStringBuilder* THIS, RogueString* value_0 )
{
  if (!!(value_0))
  {
    if (!!(THIS->indent))
    {
      {
        ROGUE_DEF_LOCAL_REF(RogueString*,_auto_207_3,(value_0));
        RogueInt32 _auto_208_4 = (0);
        for (;_auto_208_4 < _auto_207_3->character_count;++_auto_208_4)
        {
          RogueCharacter ch_5 = (RogueString_character_at(_auto_207_3,_auto_208_4));
          RogueStringBuilder__print__Character_Logical( ROGUE_ARG(THIS), ch_5, true );
        }
      }
    }
    else
    {
      {
        RogueInt32 i_1 = (0);
        RogueInt32 _auto_1_2 = (value_0->byte_count);
        for (;i_1 < _auto_1_2;++i_1)
        {
          RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), ROGUE_ARG(value_0->utf8[ i_1 ]) );
        }
      }
      THIS->count += value_0->character_count;
      if (((!!(value_0->character_count)) && (((RogueString__last( value_0 ))) == (RogueCharacter)10)))
      {
        THIS->at_newline = true;
      }
    }
    return (RogueStringBuilder*)(THIS);
  }
  else
  {
    return (RogueStringBuilder*)(((RogueStringBuilder__print__String( ROGUE_ARG(THIS), Rogue_literal_strings[1] ))));
  }
}

void RogueStringBuilder__print_indent( RogueStringBuilder* THIS )
{
  if (((!(((RogueStringBuilder__needs_indent( ROGUE_ARG(THIS) ))))) || (THIS->indent == 0)))
  {
    return;
  }
  {
    RogueInt32 i_0 = (1);
    RogueInt32 _auto_2_1 = (THIS->indent);
    for (;i_0 <= _auto_2_1;++i_0)
    {
      RogueByte_List__add__Byte( ROGUE_ARG(THIS->utf8), 32 );
    }
  }
  THIS->count += THIS->indent;
  THIS->at_newline = false;
}

RogueStringBuilder* RogueStringBuilder__println( RogueStringBuilder* THIS )
{
  return (RogueStringBuilder*)(((RogueStringBuilder__print__Character_Logical( ROGUE_ARG(THIS), (RogueCharacter)10, true ))));
}

RogueStringBuilder* RogueStringBuilder__println__String( RogueStringBuilder* THIS, RogueString* value_0 )
{
  return (RogueStringBuilder*)(((RogueStringBuilder__print__Character_Logical( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(THIS), value_0 )))), (RogueCharacter)10, true ))));
}

RogueStringBuilder* RogueStringBuilder__reserve__Int32( RogueStringBuilder* THIS, RogueInt32 additional_bytes_0 )
{
  RogueByte_List__reserve__Int32( ROGUE_ARG(THIS->utf8), additional_bytes_0 );
  return (RogueStringBuilder*)(THIS);
}

RogueByte_List* RogueByte_List__init_object( RogueByte_List* THIS )
{
  RogueGenericList__init_object( ROGUE_ARG(((RogueClassGenericList*)THIS)) );
  return (RogueByte_List*)(THIS);
}

RogueByte_List* RogueByte_List__init( RogueByte_List* THIS )
{
  RogueByte_List__init__Int32( ROGUE_ARG(THIS), 0 );
  return (RogueByte_List*)(THIS);
}

RogueString* RogueByte_List__to_String( RogueByte_List* THIS )
{
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,buffer_0,(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))));
  RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)'[', true );
  RogueLogical first_1 = (true);
  {
    ROGUE_DEF_LOCAL_REF(RogueByte_List*,_auto_219_2,(THIS));
    RogueInt32 _auto_220_3 = (0);
    for (;_auto_220_3 < _auto_219_2->count;++_auto_220_3)
    {
      RogueByte value_4 = (_auto_219_2->data->as_bytes[_auto_220_3]);
      if (first_1)
      {
        first_1 = ((RogueLogical)false);
      }
      else
      {
        RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)',', true );
      }
      if ((false))
      {
      }
      else
      {
        RogueStringBuilder__print__String( buffer_0, ROGUE_ARG(((RogueByte__to_String( value_4 )))) );
      }
    }
  }
  RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)']', true );
  return (RogueString*)(((RogueStringBuilder__to_String( buffer_0 ))));
}

RogueString* RogueByte_List__type_name( RogueByte_List* THIS )
{
  return (RogueString*)(Rogue_literal_strings[100]);
}

RogueByte_List* RogueByte_List__init__Int32( RogueByte_List* THIS, RogueInt32 initial_capacity_0 )
{
  if (!!(initial_capacity_0))
  {
    THIS->data = RogueType_create_array( initial_capacity_0, sizeof(RogueByte) );
  }
  return (RogueByte_List*)(THIS);
}

RogueByte_List* RogueByte_List__add__Byte( RogueByte_List* THIS, RogueByte value_0 )
{
  ((RogueByte_List__reserve__Int32( ROGUE_ARG(THIS), 1 )))->data->as_bytes[THIS->count] = value_0;
  THIS->count = ((THIS->count) + (1));
  return (RogueByte_List*)(THIS);
}

RogueInt32 RogueByte_List__capacity( RogueByte_List* THIS )
{
  if (!(!!(THIS->data)))
  {
    return (RogueInt32)(0);
  }
  return (RogueInt32)(THIS->data->count);
}

RogueByte_List* RogueByte_List__clear( RogueByte_List* THIS )
{
  RogueByte_List__discard_from__Int32( ROGUE_ARG(THIS), 0 );
  return (RogueByte_List*)(THIS);
}

RogueByte_List* RogueByte_List__discard_from__Int32( RogueByte_List* THIS, RogueInt32 index_0 )
{
  RogueByte zero_value_1 = 0;
  RogueInt32 c_2 = (THIS->count);
  while (c_2 > index_0)
  {
    --c_2;
    THIS->data->as_bytes[c_2] = zero_value_1;
  }
  THIS->count = c_2;
  return (RogueByte_List*)(THIS);
}

RogueByte_List* RogueByte_List__reserve__Int32( RogueByte_List* THIS, RogueInt32 additional_elements_0 )
{
  RogueInt32 required_capacity_1 = (((THIS->count) + (additional_elements_0)));
  if (!(!!(THIS->data)))
  {
    if (required_capacity_1 < 10)
    {
      required_capacity_1 = ((RogueInt32)10);
    }
    THIS->data = RogueType_create_array( required_capacity_1, sizeof(RogueByte) );
  }
  else if (required_capacity_1 > THIS->data->count)
  {
    RogueInt32 cap_2 = (((RogueByte_List__capacity( ROGUE_ARG(THIS) ))));
    if (required_capacity_1 < ((cap_2) + (cap_2)))
    {
      required_capacity_1 = ((RogueInt32)((cap_2) + (cap_2)));
    }
    ROGUE_DEF_LOCAL_REF(RogueArray*,new_data_3,(RogueType_create_array( required_capacity_1, sizeof(RogueByte) )));
    RogueArray_set(new_data_3,0,((RogueArray*)(THIS->data)),0,-1);
    THIS->data = new_data_3;
  }
  return (RogueByte_List*)(THIS);
}

RogueClassGenericList* RogueGenericList__init_object( RogueClassGenericList* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassGenericList*)(THIS);
}

RogueString* RogueGenericList__type_name( RogueClassGenericList* THIS )
{
  return (RogueString*)(Rogue_literal_strings[76]);
}

RogueString* RogueByte__to_String( RogueByte THIS )
{
  return (RogueString*)(((RogueString__operatorPLUS__Int32( ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], Rogue_literal_strings[0] ))) ))), ROGUE_ARG(((RogueInt32)(THIS))) ))));
}

RogueString* RogueArray_Byte___type_name( RogueArray* THIS )
{
  return (RogueString*)(Rogue_literal_strings[106]);
}

RogueString* RogueNativeArray__type_name( RogueArray* THIS )
{
  return (RogueString*)(Rogue_literal_strings[78]);
}

RogueInt32 RogueInt32__or_smaller__Int32( RogueInt32 THIS, RogueInt32 other_0 )
{
  return (RogueInt32)(((((THIS <= other_0))) ? (THIS) : other_0));
}

RogueCharacter RogueInt32__to_digit( RogueInt32 THIS )
{
  if (((THIS >= 0) && (THIS <= 9)))
  {
    return (RogueCharacter)(((RogueCharacter)(((THIS) + (48)))));
  }
  if (((THIS >= 10) && (THIS <= 35)))
  {
    return (RogueCharacter)(((RogueCharacter)(((((THIS) - (10))) + (65)))));
  }
  return (RogueCharacter)((RogueCharacter)'0');
}

RogueFunction___List* RogueFunction___List__init_object( RogueFunction___List* THIS )
{
  RogueGenericList__init_object( ROGUE_ARG(((RogueClassGenericList*)THIS)) );
  return (RogueFunction___List*)(THIS);
}

RogueFunction___List* RogueFunction___List__init( RogueFunction___List* THIS )
{
  RogueFunction___List__init__Int32( ROGUE_ARG(THIS), 0 );
  return (RogueFunction___List*)(THIS);
}

RogueString* RogueFunction___List__to_String( RogueFunction___List* THIS )
{
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,buffer_0,(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))));
  RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)'[', true );
  RogueLogical first_1 = (true);
  {
    ROGUE_DEF_LOCAL_REF(RogueFunction___List*,_auto_266_2,(THIS));
    RogueInt32 _auto_267_3 = (0);
    for (;_auto_267_3 < _auto_266_2->count;++_auto_267_3)
    {
      ROGUE_DEF_LOCAL_REF(RogueClassFunction__*,value_4,(((RogueClassFunction__*)(_auto_266_2->data->as_objects[_auto_267_3]))));
      if (first_1)
      {
        first_1 = ((RogueLogical)false);
      }
      else
      {
        RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)',', true );
      }
      if (((void*)value_4) == ((void*)NULL))
      {
        RogueStringBuilder__print__String( buffer_0, Rogue_literal_strings[1] );
      }
      else
      {
        RogueStringBuilder__print__String( buffer_0, ROGUE_ARG((Rogue_call_ROGUEM2( 11, ((RogueObject*)value_4) ))) );
      }
    }
  }
  RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)']', true );
  return (RogueString*)(((RogueStringBuilder__to_String( buffer_0 ))));
}

RogueString* RogueFunction___List__type_name( RogueFunction___List* THIS )
{
  return (RogueString*)(Rogue_literal_strings[103]);
}

RogueFunction___List* RogueFunction___List__init__Int32( RogueFunction___List* THIS, RogueInt32 initial_capacity_0 )
{
  if (!!(initial_capacity_0))
  {
    THIS->data = RogueType_create_array( initial_capacity_0, sizeof(RogueClassFunction__*), true );
  }
  return (RogueFunction___List*)(THIS);
}

RogueFunction___List* RogueFunction___List__add__Function__( RogueFunction___List* THIS, RogueClassFunction__* value_0 )
{
  ((RogueFunction___List__reserve__Int32( ROGUE_ARG(THIS), 1 )))->data->as_objects[THIS->count] = value_0;
  THIS->count = ((THIS->count) + (1));
  return (RogueFunction___List*)(THIS);
}

RogueInt32 RogueFunction___List__capacity( RogueFunction___List* THIS )
{
  if (!(!!(THIS->data)))
  {
    return (RogueInt32)(0);
  }
  return (RogueInt32)(THIS->data->count);
}

RogueFunction___List* RogueFunction___List__reserve__Int32( RogueFunction___List* THIS, RogueInt32 additional_elements_0 )
{
  RogueInt32 required_capacity_1 = (((THIS->count) + (additional_elements_0)));
  if (!(!!(THIS->data)))
  {
    if (required_capacity_1 < 10)
    {
      required_capacity_1 = ((RogueInt32)10);
    }
    THIS->data = RogueType_create_array( required_capacity_1, sizeof(RogueClassFunction__*), true );
  }
  else if (required_capacity_1 > THIS->data->count)
  {
    RogueInt32 cap_2 = (((RogueFunction___List__capacity( ROGUE_ARG(THIS) ))));
    if (required_capacity_1 < ((cap_2) + (cap_2)))
    {
      required_capacity_1 = ((RogueInt32)((cap_2) + (cap_2)));
    }
    ROGUE_DEF_LOCAL_REF(RogueArray*,new_data_3,(RogueType_create_array( required_capacity_1, sizeof(RogueClassFunction__*), true )));
    RogueArray_set(new_data_3,0,((RogueArray*)(THIS->data)),0,-1);
    THIS->data = new_data_3;
  }
  return (RogueFunction___List*)(THIS);
}

void RogueFunction____call( RogueObject* THIS )
{
  switch (THIS->type->index)
  {
    case 32:
      RogueFunction_190__call( (RogueClassFunction_190*)THIS );
    return;
    case 39:
      RogueFunction_623__call( (RogueClassFunction_623*)THIS );
    return;
  }
}

RogueString* RogueArray_Function_____type_name( RogueArray* THIS )
{
  return (RogueString*)(Rogue_literal_strings[105]);
}

RogueException* RogueException__init_object( RogueException* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  THIS->stack_trace = ((RogueStackTrace__init__Int32( ROGUE_ARG(ROGUE_CREATE_REF(RogueClassStackTrace*,ROGUE_CREATE_OBJECT(StackTrace))), 1 )));
  return (RogueException*)(THIS);
}

RogueException* RogueException__init( RogueException* THIS )
{
  THIS->message = (Rogue_call_ROGUEM15( 16, ROGUE_ARG(THIS) ));
  return (RogueException*)(THIS);
}

RogueString* RogueException__to_String( RogueException* THIS )
{
  return (RogueString*)(THIS->message);
}

RogueString* RogueException__type_name( RogueException* THIS )
{
  return (RogueString*)(Rogue_literal_strings[6]);
}

RogueException* RogueException__init__String( RogueException* THIS, RogueString* _auto_59_0 )
{
  THIS->message = _auto_59_0;
  return (RogueException*)(THIS);
}

void RogueException__display( RogueException* THIS )
{
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,builder_0,(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))));
  RogueStringBuilder__println__String( builder_0, ROGUE_ARG((RogueString__operatorTIMES__String_Int32( Rogue_literal_strings[7], ROGUE_ARG(((RogueInt32__or_smaller__Int32( ROGUE_ARG(((((RogueConsole__width( ((RogueClassConsole*)ROGUE_SINGLETON(Console)) )))) - (1))), 79 )))) ))) );
  RogueStringBuilder__println__String( builder_0, ROGUE_ARG((Rogue_call_ROGUEM15( 16, ROGUE_ARG(THIS) ))) );
  RogueStringBuilder__println__String( builder_0, ROGUE_ARG(((RogueString_List__join__String( ROGUE_ARG(((RogueString__word_wrap__Int32_String( ROGUE_ARG(THIS->message), 79, Rogue_literal_strings[8] )))), Rogue_literal_strings[9] )))) );
  if (!!(THIS->stack_trace->entries->count))
  {
    RogueStringBuilder__println( builder_0 );
    RogueStringBuilder__println__String( builder_0, ROGUE_ARG(((RogueString__trimmed( ROGUE_ARG(((RogueStackTrace__to_String( ROGUE_ARG(THIS->stack_trace) )))) )))) );
  }
  RogueStringBuilder__println__String( builder_0, ROGUE_ARG((RogueString__operatorTIMES__String_Int32( Rogue_literal_strings[7], ROGUE_ARG(((RogueInt32__or_smaller__Int32( ROGUE_ARG(((((RogueConsole__width( ((RogueClassConsole*)ROGUE_SINGLETON(Console)) )))) - (1))), 79 )))) ))) );
  RogueGlobal__println__Object( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), ROGUE_ARG(((RogueObject*)(builder_0))) );
}

RogueString* RogueException__format( RogueException* THIS )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,st_0,(((RogueStackTrace__to_String( ROGUE_ARG(THIS->stack_trace) )))));
  if (((void*)st_0) == ((void*)NULL))
  {
    st_0 = ((RogueString*)Rogue_literal_strings[14]);
  }
  st_0 = ((RogueString*)((RogueString__trimmed( st_0 ))));
  if (!!(st_0->character_count))
  {
    st_0 = ((RogueString*)(RogueString__operatorPLUS__String_String( Rogue_literal_strings[9], st_0 )));
  }
  return (RogueString*)((RogueString__operatorPLUS__String_String( ROGUE_ARG(((((THIS))) ? (ROGUE_ARG(((RogueException__to_String( ROGUE_ARG(THIS) ))))) : ROGUE_ARG(Rogue_literal_strings[15]))), st_0 )));
}

RogueInt32 RogueString__hash_code( RogueString* THIS )
{
  return (RogueInt32)(THIS->hash_code);
}

RogueString* RogueString__to_String( RogueString* THIS )
{
  return (RogueString*)(THIS);
}

RogueString* RogueString__type_name( RogueString* THIS )
{
  return (RogueString*)(Rogue_literal_strings[75]);
}

RogueString* RogueString__after_first__String( RogueString* THIS, RogueString* st_0 )
{
  RogueOptionalInt32 i_1 = (((RogueString__locate__String_OptionalInt32( ROGUE_ARG(THIS), st_0, ROGUE_ARG((RogueOptionalInt32__create())) ))));
  if (i_1.exists)
  {
    return (RogueString*)(((RogueString__from__Int32( ROGUE_ARG(THIS), ROGUE_ARG(((i_1.value) + (st_0->character_count))) ))));
  }
  else
  {
    return (RogueString*)(Rogue_literal_strings[0]);
  }
}

RogueString* RogueString__before_first__Character( RogueString* THIS, RogueCharacter ch_0 )
{
  RogueOptionalInt32 i_1 = (((RogueString__locate__Character_OptionalInt32( ROGUE_ARG(THIS), ch_0, ROGUE_ARG((RogueOptionalInt32__create())) ))));
  if (i_1.exists)
  {
    return (RogueString*)(((RogueString__from__Int32_Int32( ROGUE_ARG(THIS), 0, ROGUE_ARG(((i_1.value) - (1))) ))));
  }
  else
  {
    return (RogueString*)(THIS);
  }
}

RogueLogical RogueString__begins_with__Character( RogueString* THIS, RogueCharacter ch_0 )
{
  return (RogueLogical)(((!!(THIS->character_count)) && (RogueString_character_at(THIS,0) == ch_0)));
}

RogueLogical RogueString__contains__Character( RogueString* THIS, RogueCharacter ch_0 )
{
  return (RogueLogical)(((RogueString__locate__Character_OptionalInt32( ROGUE_ARG(THIS), ch_0, ROGUE_ARG((RogueOptionalInt32__create())) ))).exists);
}

RogueLogical RogueString__contains__String( RogueString* THIS, RogueString* substring_0 )
{
  return (RogueLogical)(((RogueString__locate__String_OptionalInt32( ROGUE_ARG(THIS), substring_0, ROGUE_ARG((RogueOptionalInt32__create())) ))).exists);
}

RogueLogical RogueString__contains_at__String_Int32( RogueString* THIS, RogueString* substring_0, RogueInt32 at_index_1 )
{
  if (at_index_1 < 0)
  {
    return (RogueLogical)(false);
  }
  RogueInt32 offset = RogueString_set_cursor( THIS, at_index_1 );
  RogueInt32 other_count = substring_0->byte_count;
  if (offset + other_count > THIS->byte_count) return false;
  return (0 == memcmp(THIS->utf8 + offset, substring_0->utf8, other_count));

}

RogueLogical RogueString__ends_with__Character( RogueString* THIS, RogueCharacter ch_0 )
{
  return (RogueLogical)(((THIS->character_count > 0) && (RogueString_character_at(THIS,((THIS->character_count) - (1))) == ch_0)));
}

RogueLogical RogueString__ends_with__String( RogueString* THIS, RogueString* other_0 )
{
  RogueInt32 other_count_1 = (other_0->character_count);
  return (RogueLogical)(((((THIS->character_count >= other_count_1) && (other_count_1 > 0))) && (((RogueString__contains_at__String_Int32( ROGUE_ARG(THIS), other_0, ROGUE_ARG(((THIS->character_count) - (other_count_1))) ))))));
}

RogueString* RogueString__from__Int32( RogueString* THIS, RogueInt32 i1_0 )
{
  return (RogueString*)(((RogueString__from__Int32_Int32( ROGUE_ARG(THIS), i1_0, ROGUE_ARG(((THIS->character_count) - (1))) ))));
}

RogueString* RogueString__from__Int32_Int32( RogueString* THIS, RogueInt32 i1_0, RogueInt32 i2_1 )
{
  if (i1_0 < 0)
  {
    i1_0 = ((RogueInt32)0);
  }
  else if (i2_1 >= THIS->character_count)
  {
    i2_1 = ((RogueInt32)((THIS->character_count) - (1)));
  }
  if (i1_0 > i2_1)
  {
    return (RogueString*)(Rogue_literal_strings[0]);
  }
  if (i1_0 == i2_1)
  {
    return (RogueString*)(((RogueString__operatorPLUS__Character( ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], Rogue_literal_strings[0] ))), ROGUE_ARG(RogueString_character_at(THIS,i1_0)) ))));
  }
  RogueInt32 byte_i1 = RogueString_set_cursor( THIS, i1_0 );
  RogueInt32 byte_limit = RogueString_set_cursor( THIS, i2_1+1 );
  int new_count = (byte_limit - byte_i1);
  RogueString* result = RogueString_create_with_byte_count( new_count );
  memcpy( result->utf8, THIS->utf8+byte_i1, new_count );
  return RogueString_validate( result );

}

RogueString* RogueString__from_first__Character( RogueString* THIS, RogueCharacter ch_0 )
{
  RogueOptionalInt32 i_1 = (((RogueString__locate__Character_OptionalInt32( ROGUE_ARG(THIS), ch_0, ROGUE_ARG((RogueOptionalInt32__create())) ))));
  if (!(i_1.exists))
  {
    return (RogueString*)(Rogue_literal_strings[0]);
  }
  return (RogueString*)(((RogueString__from__Int32( ROGUE_ARG(THIS), ROGUE_ARG(i_1.value) ))));
}

RogueCharacter RogueString__last( RogueString* THIS )
{
  return (RogueCharacter)(RogueString_character_at(THIS,((THIS->character_count) - (1))));
}

RogueString* RogueString__left_justified__Int32_Character( RogueString* THIS, RogueInt32 spaces_0, RogueCharacter fill_1 )
{
  if (THIS->character_count >= spaces_0)
  {
    return (RogueString*)(THIS);
  }
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,buffer_2,(((RogueStringBuilder__init__Int32( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))), spaces_0 )))));
  RogueStringBuilder__print__String( buffer_2, ROGUE_ARG(THIS) );
  {
    RogueInt32 _auto_30_3 = (THIS->character_count);
    RogueInt32 _auto_31_4 = (spaces_0);
    for (;_auto_30_3 < _auto_31_4;++_auto_30_3)
    {
      RogueStringBuilder__print__Character_Logical( buffer_2, fill_1, true );
    }
  }
  return (RogueString*)(((RogueStringBuilder__to_String( buffer_2 ))));
}

RogueString* RogueString__leftmost__Int32( RogueString* THIS, RogueInt32 n_0 )
{
  if (n_0 >= 0)
  {
    return (RogueString*)(((RogueString__from__Int32_Int32( ROGUE_ARG(THIS), 0, ROGUE_ARG(((n_0) - (1))) ))));
  }
  else
  {
    return (RogueString*)(((RogueString__from__Int32_Int32( ROGUE_ARG(THIS), 0, ROGUE_ARG(((((THIS->character_count) + (n_0))) - (1))) ))));
  }
}

RogueOptionalInt32 RogueString__locate__Character_OptionalInt32( RogueString* THIS, RogueCharacter ch_0, RogueOptionalInt32 optional_i1_1 )
{
  RogueInt32 i_2 = (0);
  RogueInt32 limit_3 = (THIS->character_count);
  if (optional_i1_1.exists)
  {
    i_2 = ((RogueInt32)optional_i1_1.value);
  }
  while (i_2 < limit_3)
  {
    if (RogueString_character_at(THIS,i_2) == ch_0)
    {
      return (RogueOptionalInt32)(RogueOptionalInt32( i_2, true ));
    }
    ++i_2;
  }
  return (RogueOptionalInt32)((RogueOptionalInt32__create()));
}

RogueOptionalInt32 RogueString__locate__String_OptionalInt32( RogueString* THIS, RogueString* other_0, RogueOptionalInt32 optional_i1_1 )
{
  RogueInt32 other_count_2 = (other_0->character_count);
  if (other_count_2 == 1)
  {
    return (RogueOptionalInt32)(((RogueString__locate__Character_OptionalInt32( ROGUE_ARG(THIS), ROGUE_ARG(RogueString_character_at(other_0,0)), optional_i1_1 ))));
  }
  RogueInt32 this_limit_3 = (((((THIS->character_count) - (other_count_2))) + (1)));
  if (((other_count_2 == 0) || (this_limit_3 <= 0)))
  {
    return (RogueOptionalInt32)((RogueOptionalInt32__create()));
  }
  RogueInt32 i1_4 = 0;
  if (optional_i1_1.exists)
  {
    i1_4 = ((RogueInt32)((optional_i1_1.value) - (1)));
    if (i1_4 < -1)
    {
      i1_4 = ((RogueInt32)-1);
    }
  }
  else
  {
    i1_4 = ((RogueInt32)-1);
  }
  while (++i1_4 < this_limit_3)
  {
    if (((RogueString__contains_at__String_Int32( ROGUE_ARG(THIS), other_0, i1_4 ))))
    {
      return (RogueOptionalInt32)(RogueOptionalInt32( i1_4, true ));
    }
  }
  return (RogueOptionalInt32)((RogueOptionalInt32__create()));
}

RogueOptionalInt32 RogueString__locate_last__Character_OptionalInt32( RogueString* THIS, RogueCharacter ch_0, RogueOptionalInt32 starting_index_1 )
{
  RogueInt32 i_2 = (((THIS->character_count) - (1)));
  if (starting_index_1.exists)
  {
    i_2 = ((RogueInt32)starting_index_1.value);
  }
  while (i_2 >= 0)
  {
    if (RogueString_character_at(THIS,i_2) == ch_0)
    {
      return (RogueOptionalInt32)(RogueOptionalInt32( i_2, true ));
    }
    --i_2;
  }
  return (RogueOptionalInt32)((RogueOptionalInt32__create()));
}

RogueString* RogueString__operatorPLUS__Character( RogueString* THIS, RogueCharacter value_0 )
{
  return (RogueString*)(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__Character_Logical( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG(THIS) )))), value_0, true )))) ))));
}

RogueString* RogueString__operatorPLUS__Int32( RogueString* THIS, RogueInt32 value_0 )
{
  return (RogueString*)(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__Int32( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG(THIS) )))), value_0 )))) ))));
}

RogueLogical RogueString__operatorEQUALSEQUALS__String( RogueString* THIS, RogueString* value_0 )
{
  if (((void*)value_0) == ((void*)NULL))
  {
    return (RogueLogical)(false);
  }
  if (((((RogueString__hash_code( ROGUE_ARG(THIS) ))) != ((RogueString__hash_code( value_0 )))) || (THIS->character_count != value_0->character_count)))
  {
    return (RogueLogical)(false);
  }
  return (RogueLogical)((0==memcmp(THIS->utf8,value_0->utf8,THIS->byte_count)));
}

RogueString* RogueString__operatorPLUS__String( RogueString* THIS, RogueString* value_0 )
{
  if (((void*)value_0) == ((void*)NULL))
  {
    return (RogueString*)((RogueString__operatorPLUS__String_String( ROGUE_ARG(THIS), Rogue_literal_strings[1] )));
  }
  if (THIS->character_count == 0)
  {
    return (RogueString*)(value_0);
  }
  if (value_0->character_count == 0)
  {
    return (RogueString*)(THIS);
  }
  return (RogueString*)(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__print__String( ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), ROGUE_ARG(THIS) )))), value_0 )))) ))));
}

RogueString* RogueString__replacing__Character_Character( RogueString* THIS, RogueCharacter look_for_0, RogueCharacter replace_with_1 )
{
  if (!(((RogueString__contains__Character( ROGUE_ARG(THIS), look_for_0 )))))
  {
    return (RogueString*)(THIS);
  }
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,result_2,(((RogueStringBuilder__init__Int32( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))), ROGUE_ARG(THIS->character_count) )))));
  {
    ROGUE_DEF_LOCAL_REF(RogueString*,_auto_110_3,(THIS));
    RogueInt32 _auto_111_4 = (0);
    for (;_auto_111_4 < _auto_110_3->character_count;++_auto_111_4)
    {
      RogueCharacter ch_5 = (RogueString_character_at(_auto_110_3,_auto_111_4));
      if (ch_5 == look_for_0)
      {
        RogueStringBuilder__print__Character_Logical( result_2, replace_with_1, true );
      }
      else
      {
        RogueStringBuilder__print__Character_Logical( result_2, ch_5, true );
      }
    }
  }
  return (RogueString*)(((RogueStringBuilder__to_String( result_2 ))));
}

RogueString_List* RogueString__split__Character( RogueString* THIS, RogueCharacter separator_0 )
{
  ROGUE_DEF_LOCAL_REF(RogueString_List*,result_1,(((RogueString_List__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueString_List*,ROGUE_CREATE_OBJECT(String_List))) )))));
  RogueInt32 i1_2 = (0);
  RogueOptionalInt32 i2_3 = (((RogueString__locate__Character_OptionalInt32( ROGUE_ARG(THIS), separator_0, ROGUE_ARG(RogueOptionalInt32( i1_2, true )) ))));
  while (i2_3.exists)
  {
    RogueString_List__add__String( result_1, ROGUE_ARG(((RogueString__from__Int32_Int32( ROGUE_ARG(THIS), i1_2, ROGUE_ARG(((i2_3.value) - (1))) )))) );
    i1_2 = ((RogueInt32)((i2_3.value) + (1)));
    i2_3 = ((RogueOptionalInt32)((RogueString__locate__Character_OptionalInt32( ROGUE_ARG(THIS), separator_0, ROGUE_ARG(RogueOptionalInt32( i1_2, true )) ))));
  }
  RogueString_List__add__String( result_1, ROGUE_ARG(((RogueString__from__Int32( ROGUE_ARG(THIS), i1_2 )))) );
  return (RogueString_List*)(result_1);
}

RogueString* RogueString__times__Int32( RogueString* THIS, RogueInt32 n_0 )
{
  if (n_0 <= 0)
  {
    return (RogueString*)(Rogue_literal_strings[0]);
  }
  if (n_0 == 1)
  {
    return (RogueString*)(THIS);
  }
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,builder_1,(((RogueStringBuilder__init__Int32( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))), ROGUE_ARG(((THIS->character_count) * (n_0))) )))));
  {
    RogueInt32 _auto_36_2 = (1);
    RogueInt32 _auto_37_3 = (n_0);
    for (;_auto_36_2 <= _auto_37_3;++_auto_36_2)
    {
      RogueStringBuilder__print__String( builder_1, ROGUE_ARG(THIS) );
    }
  }
  return (RogueString*)(((RogueStringBuilder__to_String( builder_1 ))));
}

RogueString* RogueString__to_lowercase( RogueString* THIS )
{
  RogueLogical has_uc_0 = (false);
  {
    ROGUE_DEF_LOCAL_REF(RogueString*,_auto_131_2,(THIS));
    RogueInt32 _auto_132_3 = (0);
    for (;_auto_132_3 < _auto_131_2->character_count;++_auto_132_3)
    {
      RogueCharacter ch_4 = (RogueString_character_at(_auto_131_2,_auto_132_3));
      if (((ch_4 >= (RogueCharacter)'A') && (ch_4 <= (RogueCharacter)'Z')))
      {
        has_uc_0 = ((RogueLogical)true);
        goto _auto_133;
      }
    }
  }
  _auto_133:;
  if (!(has_uc_0))
  {
    return (RogueString*)(THIS);
  }
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,result_1,(((RogueStringBuilder__init__Int32( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))), ROGUE_ARG(THIS->character_count) )))));
  {
    ROGUE_DEF_LOCAL_REF(RogueString*,_auto_134_5,(THIS));
    RogueInt32 _auto_135_6 = (0);
    for (;_auto_135_6 < _auto_134_5->character_count;++_auto_135_6)
    {
      RogueCharacter ch_7 = (RogueString_character_at(_auto_134_5,_auto_135_6));
      if (((ch_7 >= (RogueCharacter)'A') && (ch_7 <= (RogueCharacter)'Z')))
      {
        RogueStringBuilder__print__Character_Logical( result_1, ROGUE_ARG(((((ch_7) - ((RogueCharacter)'A'))) + ((RogueCharacter)'a'))), true );
      }
      else
      {
        RogueStringBuilder__print__Character_Logical( result_1, ch_7, true );
      }
    }
  }
  return (RogueString*)(((RogueStringBuilder__to_String( result_1 ))));
}

RogueString* RogueString__trimmed( RogueString* THIS )
{
  RogueInt32 i1_0 = (0);
  RogueInt32 i2_1 = (((THIS->character_count) - (1)));
  while (i1_0 <= i2_1)
  {
    if (RogueString_character_at(THIS,i1_0) <= (RogueCharacter)' ')
    {
      ++i1_0;
    }
    else if (RogueString_character_at(THIS,i2_1) <= (RogueCharacter)' ')
    {
      --i2_1;
    }
    else
    {
      goto _auto_141;
    }
  }
  _auto_141:;
  if (i1_0 > i2_1)
  {
    return (RogueString*)(Rogue_literal_strings[0]);
  }
  if (((i1_0 == 0) && (i2_1 == ((THIS->character_count) - (1)))))
  {
    return (RogueString*)(THIS);
  }
  return (RogueString*)(((RogueString__from__Int32_Int32( ROGUE_ARG(THIS), i1_0, i2_1 ))));
}

RogueString_List* RogueString__word_wrap__Int32_String( RogueString* THIS, RogueInt32 width_0, RogueString* allow_break_after_1 )
{
  return (RogueString_List*)(((RogueString__split__Character( ROGUE_ARG(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueString__word_wrap__Int32_StringBuilder_String( ROGUE_ARG(THIS), width_0, ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))), allow_break_after_1 )))) )))), (RogueCharacter)10 ))));
}

RogueStringBuilder* RogueString__word_wrap__Int32_StringBuilder_String( RogueString* THIS, RogueInt32 width_0, RogueStringBuilder* buffer_1, RogueString* allow_break_after_2 )
{
  RogueInt32 i1_3 = 0;
  RogueInt32 i2_4 = 0;
  RogueInt32 len_5 = (THIS->character_count);
  if (len_5 == 0)
  {
    return (RogueStringBuilder*)(buffer_1);
  }
  RogueInt32 w_6 = (width_0);
  RogueInt32 initial_indent_7 = (0);
  {
    ROGUE_DEF_LOCAL_REF(RogueString*,_auto_142_19,(THIS));
    RogueInt32 _auto_143_20 = (0);
    for (;_auto_143_20 < _auto_142_19->character_count;++_auto_143_20)
    {
      RogueCharacter ch_21 = (RogueString_character_at(_auto_142_19,_auto_143_20));
      if (ch_21 != (RogueCharacter)' ')
      {
        goto _auto_144;
      }
      ++initial_indent_7;
      --w_6;
      ++i1_3;
    }
  }
  _auto_144:;
  if (w_6 <= 0)
  {
    w_6 = ((RogueInt32)width_0);
    initial_indent_7 = ((RogueInt32)0);
    RogueStringBuilder__println( buffer_1 );
  }
  else
  {
    {
      RogueInt32 _auto_39_8 = (1);
      RogueInt32 _auto_40_9 = (((width_0) - (w_6)));
      for (;_auto_39_8 <= _auto_40_9;++_auto_39_8)
      {
        RogueStringBuilder__print__Character_Logical( buffer_1, (RogueCharacter)' ', true );
      }
    }
  }
  RogueLogical needs_newline_10 = (false);
  while (i2_4 < len_5)
  {
    while (((((((i2_4) - (i1_3)) < w_6) && (i2_4 < len_5))) && (RogueString_character_at(THIS,i2_4) != (RogueCharacter)10)))
    {
      ++i2_4;
    }
    if (((i2_4) - (i1_3)) == w_6)
    {
      if (i2_4 >= len_5)
      {
        i2_4 = ((RogueInt32)len_5);
      }
      else if (RogueString_character_at(THIS,i2_4) != (RogueCharacter)10)
      {
        while (((RogueString_character_at(THIS,i2_4) != (RogueCharacter)' ') && (i2_4 > i1_3)))
        {
          --i2_4;
        }
        if (i2_4 == i1_3)
        {
          i2_4 = ((RogueInt32)((i1_3) + (w_6)));
          if (!!(allow_break_after_2))
          {
            while (((((i2_4 > i1_3) && (!(((RogueString__contains__Character( allow_break_after_2, ROGUE_ARG(RogueString_character_at(THIS,((i2_4) - (1)))) ))))))) && (i2_4 > i1_3)))
            {
              --i2_4;
            }
            if (i2_4 == i1_3)
            {
              i2_4 = ((RogueInt32)((i1_3) + (w_6)));
            }
          }
        }
      }
    }
    if (needs_newline_10)
    {
      RogueStringBuilder__println( buffer_1 );
      if (!!(initial_indent_7))
      {
        {
          RogueInt32 _auto_41_11 = (1);
          RogueInt32 _auto_42_12 = (initial_indent_7);
          for (;_auto_41_11 <= _auto_42_12;++_auto_41_11)
          {
            RogueStringBuilder__print__Character_Logical( buffer_1, (RogueCharacter)' ', true );
          }
        }
      }
    }
    {
      RogueInt32 i_13 = (i1_3);
      RogueInt32 _auto_43_14 = (((i2_4) - (1)));
      for (;i_13 <= _auto_43_14;++i_13)
      {
        RogueStringBuilder__print__Character_Logical( buffer_1, ROGUE_ARG(RogueString_character_at(THIS,i_13)), true );
      }
    }
    needs_newline_10 = ((RogueLogical)true);
    if (i2_4 == len_5)
    {
      return (RogueStringBuilder*)(buffer_1);
    }
    else
    {
      switch (RogueString_character_at(THIS,i2_4))
      {
        case (RogueCharacter)' ':
        {
          while (((i2_4 < len_5) && (RogueString_character_at(THIS,i2_4) == (RogueCharacter)' ')))
          {
            ++i2_4;
          }
          if (((i2_4 < len_5) && (RogueString_character_at(THIS,i2_4) == (RogueCharacter)10)))
          {
            ++i2_4;
          }
          i1_3 = ((RogueInt32)i2_4);
          break;
        }
        case (RogueCharacter)10:
        {
          ++i2_4;
          w_6 = ((RogueInt32)width_0);
          initial_indent_7 = ((RogueInt32)0);
          {
            RogueInt32 i_15 = (i2_4);
            RogueInt32 _auto_44_16 = (len_5);
            for (;i_15 < _auto_44_16;++i_15)
            {
              if (RogueString_character_at(THIS,i_15) != (RogueCharacter)' ')
              {
                goto _auto_145;
              }
              ++initial_indent_7;
              --w_6;
              ++i2_4;
            }
          }
          _auto_145:;
          if (w_6 <= 0)
          {
            w_6 = ((RogueInt32)width_0);
            initial_indent_7 = ((RogueInt32)0);
          }
          else
          {
            {
              RogueInt32 _auto_45_17 = (1);
              RogueInt32 _auto_46_18 = (((width_0) - (w_6)));
              for (;_auto_45_17 <= _auto_46_18;++_auto_45_17)
              {
                RogueStringBuilder__print__Character_Logical( buffer_1, (RogueCharacter)' ', true );
              }
            }
          }
          break;
        }
      }
      i1_3 = ((RogueInt32)i2_4);
    }
  }
  return (RogueStringBuilder*)(buffer_1);
}

RogueClassStackTrace* RogueStackTrace__init_object( RogueClassStackTrace* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassStackTrace*)(THIS);
}

RogueString* RogueStackTrace__to_String( RogueClassStackTrace* THIS )
{
  return (RogueString*)(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueStackTrace__print__StringBuilder( ROGUE_ARG(THIS), ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))) )))) ))));
}

RogueString* RogueStackTrace__type_name( RogueClassStackTrace* THIS )
{
  return (RogueString*)(Rogue_literal_strings[74]);
}

RogueClassStackTrace* RogueStackTrace__init__Int32( RogueClassStackTrace* THIS, RogueInt32 omit_count_0 )
{
  ++omit_count_0;
  RogueDebugTrace* current = Rogue_call_stack;
  while (current && omit_count_0 > 0)
  {
    --omit_count_0;
    current = current->previous_trace;
  }
  if (current) THIS->count = current->count();

  THIS->entries = ((RogueString_List__init__Int32( ROGUE_ARG(ROGUE_CREATE_REF(RogueString_List*,ROGUE_CREATE_OBJECT(String_List))), ROGUE_ARG(THIS->count) )));
  while (current!=0)
  {
    RogueString_List__add__String( ROGUE_ARG(THIS->entries), ROGUE_ARG(RogueString_create_from_utf8( current->to_c_string() )) );
    current = current->previous_trace;

  }
  return (RogueClassStackTrace*)(THIS);
}

void RogueStackTrace__format( RogueClassStackTrace* THIS )
{
  if (THIS->is_formatted)
  {
    return;
  }
  THIS->is_formatted = true;
  RogueInt32 max_characters_0 = (0);
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_195_2,(THIS->entries));
    RogueInt32 _auto_196_3 = (0);
    for (;_auto_196_3 < _auto_195_2->count;++_auto_196_3)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,entry_4,(((RogueString*)(_auto_195_2->data->as_objects[_auto_196_3]))));
      RogueOptionalInt32 sp_1 = (((RogueString__locate__Character_OptionalInt32( entry_4, (RogueCharacter)' ', ROGUE_ARG((RogueOptionalInt32__create())) ))));
      if (sp_1.exists)
      {
        max_characters_0 = ((RogueInt32)(RogueMath__max__Int32_Int32( max_characters_0, ROGUE_ARG(sp_1.value) )));
      }
    }
  }
  ++max_characters_0;
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_197_5,(THIS->entries));
    RogueInt32 i_6 = (0);
    for (;i_6 < _auto_197_5->count;++i_6)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,entry_7,(((RogueString*)(_auto_197_5->data->as_objects[i_6]))));
      if (((RogueString__contains__Character( entry_7, (RogueCharacter)' ' ))))
      {
        THIS->entries->data->as_objects[i_6] = (RogueString__operatorPLUS__String_String( ROGUE_ARG(((RogueString__left_justified__Int32_Character( ROGUE_ARG(((RogueString__before_first__Character( entry_7, (RogueCharacter)' ' )))), max_characters_0, (RogueCharacter)' ' )))), ROGUE_ARG(((RogueString__from_first__Character( entry_7, (RogueCharacter)' ' )))) ));
      }
    }
  }
}

void RogueStackTrace__print( RogueClassStackTrace* THIS )
{
  RogueStackTrace__print__StringBuilder( ROGUE_ARG(THIS), ROGUE_ARG(((RogueClassGlobal*)ROGUE_SINGLETON(Global))->global_output_buffer) );
  RogueGlobal__flush( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)) );
}

RogueStringBuilder* RogueStackTrace__print__StringBuilder( RogueClassStackTrace* THIS, RogueStringBuilder* buffer_0 )
{
  RogueStackTrace__format( ROGUE_ARG(THIS) );
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_198_1,(THIS->entries));
    RogueInt32 _auto_199_2 = (0);
    for (;_auto_199_2 < _auto_198_1->count;++_auto_199_2)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,entry_3,(((RogueString*)(_auto_198_1->data->as_objects[_auto_199_2]))));
      RogueStringBuilder__println__String( buffer_0, entry_3 );
    }
  }
  return (RogueStringBuilder*)(buffer_0);
}

RogueString_List* RogueString_List__init_object( RogueString_List* THIS )
{
  RogueGenericList__init_object( ROGUE_ARG(((RogueClassGenericList*)THIS)) );
  return (RogueString_List*)(THIS);
}

RogueString_List* RogueString_List__init( RogueString_List* THIS )
{
  RogueString_List__init__Int32( ROGUE_ARG(THIS), 0 );
  return (RogueString_List*)(THIS);
}

RogueString* RogueString_List__to_String( RogueString_List* THIS )
{
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,buffer_0,(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))));
  RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)'[', true );
  RogueLogical first_1 = (true);
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_317_2,(THIS));
    RogueInt32 _auto_318_3 = (0);
    for (;_auto_318_3 < _auto_317_2->count;++_auto_318_3)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,value_4,(((RogueString*)(_auto_317_2->data->as_objects[_auto_318_3]))));
      if (first_1)
      {
        first_1 = ((RogueLogical)false);
      }
      else
      {
        RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)',', true );
      }
      if (((void*)value_4) == ((void*)NULL))
      {
        RogueStringBuilder__print__String( buffer_0, Rogue_literal_strings[1] );
      }
      else
      {
        RogueStringBuilder__print__String( buffer_0, value_4 );
      }
    }
  }
  RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)']', true );
  return (RogueString*)(((RogueStringBuilder__to_String( buffer_0 ))));
}

RogueString* RogueString_List__type_name( RogueString_List* THIS )
{
  return (RogueString*)(Rogue_literal_strings[102]);
}

RogueString_List* RogueString_List__init__Int32( RogueString_List* THIS, RogueInt32 initial_capacity_0 )
{
  if (!!(initial_capacity_0))
  {
    THIS->data = RogueType_create_array( initial_capacity_0, sizeof(RogueString*), true );
  }
  return (RogueString_List*)(THIS);
}

RogueString_List* RogueString_List__add__String( RogueString_List* THIS, RogueString* value_0 )
{
  ((RogueString_List__reserve__Int32( ROGUE_ARG(THIS), 1 )))->data->as_objects[THIS->count] = value_0;
  THIS->count = ((THIS->count) + (1));
  return (RogueString_List*)(THIS);
}

RogueString_List* RogueString_List__add__String_List( RogueString_List* THIS, RogueString_List* other_0 )
{
  RogueString_List__reserve__Int32( ROGUE_ARG(THIS), ROGUE_ARG(other_0->count) );
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_325_1,(other_0));
    RogueInt32 _auto_326_2 = (0);
    for (;_auto_326_2 < _auto_325_1->count;++_auto_326_2)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,value_3,(((RogueString*)(_auto_325_1->data->as_objects[_auto_326_2]))));
      RogueString_List__add__String( ROGUE_ARG(THIS), value_3 );
    }
  }
  return (RogueString_List*)(THIS);
}

RogueInt32 RogueString_List__capacity( RogueString_List* THIS )
{
  if (!(!!(THIS->data)))
  {
    return (RogueInt32)(0);
  }
  return (RogueInt32)(THIS->data->count);
}

RogueLogical RogueString_List__is_empty( RogueString_List* THIS )
{
  return (RogueLogical)(THIS->count == 0);
}

RogueString_List* RogueString_List__reserve__Int32( RogueString_List* THIS, RogueInt32 additional_elements_0 )
{
  RogueInt32 required_capacity_1 = (((THIS->count) + (additional_elements_0)));
  if (!(!!(THIS->data)))
  {
    if (required_capacity_1 < 10)
    {
      required_capacity_1 = ((RogueInt32)10);
    }
    THIS->data = RogueType_create_array( required_capacity_1, sizeof(RogueString*), true );
  }
  else if (required_capacity_1 > THIS->data->count)
  {
    RogueInt32 cap_2 = (((RogueString_List__capacity( ROGUE_ARG(THIS) ))));
    if (required_capacity_1 < ((cap_2) + (cap_2)))
    {
      required_capacity_1 = ((RogueInt32)((cap_2) + (cap_2)));
    }
    ROGUE_DEF_LOCAL_REF(RogueArray*,new_data_3,(RogueType_create_array( required_capacity_1, sizeof(RogueString*), true )));
    RogueArray_set(new_data_3,0,((RogueArray*)(THIS->data)),0,-1);
    THIS->data = new_data_3;
  }
  return (RogueString_List*)(THIS);
}

RogueString* RogueString_List__remove_at__Int32( RogueString_List* THIS, RogueInt32 index_0 )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,result_1,(((RogueString*)(THIS->data->as_objects[index_0]))));
  RogueArray_set(THIS->data,index_0,((RogueArray*)(THIS->data)),((index_0) + (1)),-1);
  ROGUE_DEF_LOCAL_REF(RogueString*,zero_value_2,0);
  THIS->count = ((THIS->count) + (-1));
  THIS->data->as_objects[THIS->count] = zero_value_2;
  return (RogueString*)(result_1);
}

RogueString* RogueString_List__join__String( RogueString_List* THIS, RogueString* separator_0 )
{
  RogueInt32 total_count_1 = (0);
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_356_4,(THIS));
    RogueInt32 _auto_357_5 = (0);
    for (;_auto_357_5 < _auto_356_4->count;++_auto_357_5)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,line_6,(((RogueString*)(_auto_356_4->data->as_objects[_auto_357_5]))));
      total_count_1 += line_6->character_count;
    }
  }
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,builder_2,(((RogueStringBuilder__init__Int32( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))), total_count_1 )))));
  RogueLogical first_3 = (true);
  {
    ROGUE_DEF_LOCAL_REF(RogueString_List*,_auto_358_7,(THIS));
    RogueInt32 _auto_359_8 = (0);
    for (;_auto_359_8 < _auto_358_7->count;++_auto_359_8)
    {
      ROGUE_DEF_LOCAL_REF(RogueString*,line_9,(((RogueString*)(_auto_358_7->data->as_objects[_auto_359_8]))));
      if (first_3)
      {
        first_3 = ((RogueLogical)false);
      }
      else
      {
        RogueStringBuilder__print__String( builder_2, separator_0 );
      }
      RogueStringBuilder__print__String( builder_2, line_9 );
    }
  }
  return (RogueString*)(((RogueStringBuilder__to_String( builder_2 ))));
}

RogueString* RogueArray_String___type_name( RogueArray* THIS )
{
  return (RogueString*)(Rogue_literal_strings[104]);
}

RogueReal64 RogueReal64__or_smaller__Real64( RogueReal64 THIS, RogueReal64 other_0 )
{
  return (RogueReal64)(((((THIS <= other_0))) ? (THIS) : other_0));
}

RogueStringBuilder* RogueInt64__print_in_power2_base__Int32_Int32_StringBuilder( RogueInt64 THIS, RogueInt32 base_0, RogueInt32 digits_1, RogueStringBuilder* buffer_2 )
{
  RogueInt32 bits_3 = (0);
  RogueInt32 temp_4 = (base_0);
  while (temp_4 > 1)
  {
    ++bits_3;
    temp_4 = ((RogueInt32)((temp_4) >> (1)));
  }
  if (digits_1 > 1)
  {
    RogueInt64__print_in_power2_base__Int32_Int32_StringBuilder( ROGUE_ARG(((THIS) >> (((RogueInt64)(bits_3))))), base_0, ROGUE_ARG(((digits_1) - (1))), buffer_2 );
  }
  RogueStringBuilder__print__Character_Logical( buffer_2, ROGUE_ARG(((RogueInt32__to_digit( ROGUE_ARG(((RogueInt32)(((THIS) & (((RogueInt64)(((base_0) - (1))))))))) )))), true );
  return (RogueStringBuilder*)(buffer_2);
}

RogueString* RogueInt64__to_hex_string__Int32( RogueInt64 THIS, RogueInt32 digits_0 )
{
  return (RogueString*)(((RogueStringBuilder__to_String( ROGUE_ARG(((RogueInt64__print_in_power2_base__Int32_Int32_StringBuilder( ROGUE_ARG(THIS), 16, digits_0, ROGUE_ARG(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))) )))) ))));
}

RogueString* RogueCharacter__to_String( RogueCharacter THIS )
{
  return (RogueString*)(((RogueString__operatorPLUS__Character( ROGUE_ARG((RogueString__operatorPLUS__String_String( Rogue_literal_strings[0], Rogue_literal_strings[0] ))), ROGUE_ARG(THIS) ))));
}

RogueCharacter_List* RogueCharacter_List__init_object( RogueCharacter_List* THIS )
{
  RogueGenericList__init_object( ROGUE_ARG(((RogueClassGenericList*)THIS)) );
  return (RogueCharacter_List*)(THIS);
}

RogueCharacter_List* RogueCharacter_List__init( RogueCharacter_List* THIS )
{
  RogueCharacter_List__init__Int32( ROGUE_ARG(THIS), 0 );
  return (RogueCharacter_List*)(THIS);
}

RogueString* RogueCharacter_List__to_String( RogueCharacter_List* THIS )
{
  ROGUE_DEF_LOCAL_REF(RogueStringBuilder*,buffer_0,(((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )))));
  RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)'[', true );
  RogueLogical first_1 = (true);
  {
    ROGUE_DEF_LOCAL_REF(RogueCharacter_List*,_auto_559_2,(THIS));
    RogueInt32 _auto_560_3 = (0);
    for (;_auto_560_3 < _auto_559_2->count;++_auto_560_3)
    {
      RogueCharacter value_4 = (_auto_559_2->data->as_characters[_auto_560_3]);
      if (first_1)
      {
        first_1 = ((RogueLogical)false);
      }
      else
      {
        RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)',', true );
      }
      if ((false))
      {
      }
      else
      {
        RogueStringBuilder__print__String( buffer_0, ROGUE_ARG(((RogueCharacter__to_String( value_4 )))) );
      }
    }
  }
  RogueStringBuilder__print__Character_Logical( buffer_0, (RogueCharacter)']', true );
  return (RogueString*)(((RogueStringBuilder__to_String( buffer_0 ))));
}

RogueString* RogueCharacter_List__type_name( RogueCharacter_List* THIS )
{
  return (RogueString*)(Rogue_literal_strings[101]);
}

RogueCharacter_List* RogueCharacter_List__init__Int32( RogueCharacter_List* THIS, RogueInt32 initial_capacity_0 )
{
  if (!!(initial_capacity_0))
  {
    THIS->data = RogueType_create_array( initial_capacity_0, sizeof(RogueCharacter) );
  }
  return (RogueCharacter_List*)(THIS);
}

RogueString* RogueArray_Character___type_name( RogueArray* THIS )
{
  return (RogueString*)(Rogue_literal_strings[107]);
}

RogueClassConsole* RogueConsole__init_object( RogueClassConsole* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  THIS->error = ((RogueClassConsoleErrorPrinter*)((Rogue_call_ROGUEM1( 1, ROGUE_ARG(((RogueObject*)ROGUE_CREATE_REF(RogueClassConsoleErrorPrinter*,ROGUE_CREATE_OBJECT(ConsoleErrorPrinter)))) ))));
  THIS->output_buffer = ((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )));
  THIS->input_buffer = ((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )));
  return (RogueClassConsole*)(THIS);
}

RogueClassConsole* RogueConsole__init( RogueClassConsole* THIS )
{
  tcgetattr( STDIN_FILENO, &THIS->original_terminal_settings );

  RogueGlobal__on_exit__Function__( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)), ROGUE_ARG(((((RogueClassFunction__*)(((RogueFunction_623__init__Console( ROGUE_ARG(ROGUE_CREATE_REF(RogueClassFunction_623*,ROGUE_CREATE_OBJECT(Function_623))), ROGUE_ARG(THIS) )))))))) );
  THIS->io_handler = ((RogueClassConsoleIOHandler*)(((RogueClassBlockingConsoleIOHandler*)((Rogue_call_ROGUEM1( 1, ROGUE_ARG(((RogueObject*)ROGUE_CREATE_REF(RogueClassBlockingConsoleIOHandler*,ROGUE_CREATE_OBJECT(BlockingConsoleIOHandler)))) ))))));
  return (RogueClassConsole*)(THIS);
}

RogueString* RogueConsole__type_name( RogueClassConsole* THIS )
{
  return (RogueString*)(Rogue_literal_strings[79]);
}

RogueClassConsole* RogueConsole__flush( RogueClassConsole* THIS )
{
  RogueConsole__write__StringBuilder( ROGUE_ARG(THIS), ROGUE_ARG(THIS->output_buffer) );
  RogueStringBuilder__clear( ROGUE_ARG(THIS->output_buffer) );
  return (RogueClassConsole*)(THIS);
}

RogueClassConsole* RogueConsole__write__StringBuilder( RogueClassConsole* THIS, RogueStringBuilder* buffer_0 )
{
  Rogue_call_ROGUEM31( 21, ROGUE_ARG(THIS->io_handler), ROGUE_ARG(buffer_0->utf8->data), ROGUE_ARG(buffer_0->utf8->count) );
  return (RogueClassConsole*)(THIS);
}

RogueInt32 RogueConsole__width( RogueClassConsole* THIS )
{
  struct winsize sz;
  ioctl( STDOUT_FILENO, TIOCGWINSZ, &sz );
  return sz.ws_col;

}

RogueClassPrintWriter_output_buffer_* RoguePrintWriter_output_buffer___flush( RogueObject* THIS )
{
  switch (THIS->type->index)
  {
    case 25:
      return (RogueClassPrintWriter_output_buffer_*)RogueConsole__flush( (RogueClassConsole*)THIS );
    case 28:
      return (RogueClassPrintWriter_output_buffer_*)RogueConsoleErrorPrinter__flush( (RogueClassConsoleErrorPrinter*)THIS );
    default:
      return 0;
  }
}

RogueClassPrintWriter_output_buffer_* RoguePrintWriter_output_buffer___write__StringBuilder( RogueObject* THIS, RogueStringBuilder* buffer_0 )
{
  switch (THIS->type->index)
  {
    case 25:
      return (RogueClassPrintWriter_output_buffer_*)RogueConsole__write__StringBuilder( (RogueClassConsole*)THIS, buffer_0 );
    case 28:
      return (RogueClassPrintWriter_output_buffer_*)RogueConsoleErrorPrinter__write__StringBuilder( (RogueClassConsoleErrorPrinter*)THIS, buffer_0 );
    default:
      return 0;
  }
}

RogueClassConsoleErrorPrinter* RogueConsoleErrorPrinter__init_object( RogueClassConsoleErrorPrinter* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  THIS->output_buffer = ((RogueStringBuilder__init( ROGUE_ARG(ROGUE_CREATE_REF(RogueStringBuilder*,ROGUE_CREATE_OBJECT(StringBuilder))) )));
  return (RogueClassConsoleErrorPrinter*)(THIS);
}

RogueString* RogueConsoleErrorPrinter__type_name( RogueClassConsoleErrorPrinter* THIS )
{
  return (RogueString*)(Rogue_literal_strings[87]);
}

RogueClassConsoleErrorPrinter* RogueConsoleErrorPrinter__flush( RogueClassConsoleErrorPrinter* THIS )
{
  RogueConsoleErrorPrinter__write__StringBuilder( ROGUE_ARG(THIS), ROGUE_ARG(THIS->output_buffer) );
  RogueStringBuilder__clear( ROGUE_ARG(THIS->output_buffer) );
  return (RogueClassConsoleErrorPrinter*)(THIS);
}

RogueClassConsoleErrorPrinter* RogueConsoleErrorPrinter__write__StringBuilder( RogueClassConsoleErrorPrinter* THIS, RogueStringBuilder* buffer_0 )
{
  Rogue_call_ROGUEM31( 23, ROGUE_ARG(((RogueClassConsole*)ROGUE_SINGLETON(Console))->io_handler), ROGUE_ARG(buffer_0->utf8->data), ROGUE_ARG(buffer_0->utf8->count) );
  return (RogueClassConsoleErrorPrinter*)(THIS);
}

RogueClassConsoleIOHandler* RogueConsoleIOHandler__init_object( RogueClassConsoleIOHandler* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassConsoleIOHandler*)(THIS);
}

RogueString* RogueConsoleIOHandler__type_name( RogueClassConsoleIOHandler* THIS )
{
  return (RogueString*)(Rogue_literal_strings[88]);
}

RogueClassMath* RogueMath__init_object( RogueClassMath* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassMath*)(THIS);
}

RogueString* RogueMath__type_name( RogueClassMath* THIS )
{
  return (RogueString*)(Rogue_literal_strings[80]);
}

RogueClassRuntime* RogueRuntime__init_object( RogueClassRuntime* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassRuntime*)(THIS);
}

RogueString* RogueRuntime__type_name( RogueClassRuntime* THIS )
{
  return (RogueString*)(Rogue_literal_strings[81]);
}

RogueClassFunction_190* RogueFunction_190__init_object( RogueClassFunction_190* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassFunction_190*)(THIS);
}

RogueString* RogueFunction_190__type_name( RogueClassFunction_190* THIS )
{
  return (RogueString*)(Rogue_literal_strings[82]);
}

void RogueFunction_190__call( RogueClassFunction_190* THIS )
{
  RogueGlobal__flush( ((RogueClassGlobal*)ROGUE_SINGLETON(Global)) );
}

RogueClassget_platform* Rogueget_platform__init_object( RogueClassget_platform* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassget_platform*)(THIS);
}

RogueString* Rogueget_platform__type_name( RogueClassget_platform* THIS )
{
  return (RogueString*)(Rogue_literal_strings[83]);
}

RogueClassstandard_build* Roguestandard_build__init_object( RogueClassstandard_build* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassstandard_build*)(THIS);
}

RogueString* Roguestandard_build__type_name( RogueClassstandard_build* THIS )
{
  return (RogueString*)(Rogue_literal_strings[84]);
}

RogueClassSystem* RogueSystem__init_object( RogueClassSystem* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassSystem*)(THIS);
}

RogueString* RogueSystem__type_name( RogueClassSystem* THIS )
{
  return (RogueString*)(Rogue_literal_strings[85]);
}

RogueClassError* RogueError__init_object( RogueClassError* THIS )
{
  RogueException__init_object( ROGUE_ARG(((RogueException*)THIS)) );
  return (RogueClassError*)(THIS);
}

RogueString* RogueError__type_name( RogueClassError* THIS )
{
  return (RogueString*)(Rogue_literal_strings[108]);
}

RogueWeakReference* RogueWeakReference__init_object( RogueWeakReference* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueWeakReference*)(THIS);
}

RogueString* RogueWeakReference__type_name( RogueWeakReference* THIS )
{
  return (RogueString*)(Rogue_literal_strings[86]);
}

void RogueWeakReference__on_cleanup( RogueWeakReference* THIS )
{
  if (Rogue_weak_references == THIS)
  {
    Rogue_weak_references = THIS->next_weak_reference;
  }
  else
  {
    RogueWeakReference* cur = Rogue_weak_references;
    while (cur && cur->next_weak_reference != THIS)
    {
      cur = cur->next_weak_reference;
    }
    if (cur) cur->next_weak_reference = cur->next_weak_reference->next_weak_reference;
  }

}

RogueClassFile* RogueFile__init_object( RogueClassFile* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassFile*)(THIS);
}

RogueString* RogueFile__to_String( RogueClassFile* THIS )
{
  return (RogueString*)(THIS->filepath);
}

RogueString* RogueFile__type_name( RogueClassFile* THIS )
{
  return (RogueString*)(Rogue_literal_strings[89]);
}

RogueClassFunction_623* RogueFunction_623__init_object( RogueClassFunction_623* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassFunction_623*)(THIS);
}

RogueString* RogueFunction_623__type_name( RogueClassFunction_623* THIS )
{
  return (RogueString*)(Rogue_literal_strings[90]);
}

void RogueFunction_623__call( RogueClassFunction_623* THIS )
{
  tcsetattr( STDIN_FILENO, TCSANOW, &THIS->console->original_terminal_settings );

}

RogueClassFunction_623* RogueFunction_623__init__Console( RogueClassFunction_623* THIS, RogueClassConsole* _auto_624_0 )
{
  THIS->console = _auto_624_0;
  return (RogueClassFunction_623*)(THIS);
}

RogueClassBlockingConsoleIOHandler* RogueBlockingConsoleIOHandler__init_object( RogueClassBlockingConsoleIOHandler* THIS )
{
  RogueConsoleIOHandler__init_object( ROGUE_ARG(((RogueClassConsoleIOHandler*)THIS)) );
  return (RogueClassBlockingConsoleIOHandler*)(THIS);
}

RogueString* RogueBlockingConsoleIOHandler__type_name( RogueClassBlockingConsoleIOHandler* THIS )
{
  return (RogueString*)(Rogue_literal_strings[109]);
}

void RogueBlockingConsoleIOHandler__write__Array_Int32( RogueClassBlockingConsoleIOHandler* THIS, RogueArray* bytes_0, RogueInt32 count_1 )
{
  fwrite( bytes_0->as_bytes, 1, count_1, stdout );

}

void RogueBlockingConsoleIOHandler__write_error__Array_Int32( RogueClassBlockingConsoleIOHandler* THIS, RogueArray* bytes_0, RogueInt32 count_1 )
{
  fwrite( bytes_0->as_bytes, 1, count_1, stderr );

}

RogueClassBuildConfig* RogueBuildConfig__init_object( RogueClassBuildConfig* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassBuildConfig*)(THIS);
}

RogueString* RogueBuildConfig__type_name( RogueClassBuildConfig* THIS )
{
  return (RogueString*)(Rogue_literal_strings[91]);
}

RogueClassinstall_emscripten* Rogueinstall_emscripten__init_object( RogueClassinstall_emscripten* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassinstall_emscripten*)(THIS);
}

RogueString* Rogueinstall_emscripten__type_name( RogueClassinstall_emscripten* THIS )
{
  return (RogueString*)(Rogue_literal_strings[92]);
}

RogueClassconfigure_build_folder* Rogueconfigure_build_folder__init_object( RogueClassconfigure_build_folder* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassconfigure_build_folder*)(THIS);
}

RogueString* Rogueconfigure_build_folder__type_name( RogueClassconfigure_build_folder* THIS )
{
  return (RogueString*)(Rogue_literal_strings[93]);
}

RogueClasscompile* Roguecompile__init_object( RogueClasscompile* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClasscompile*)(THIS);
}

RogueString* Roguecompile__type_name( RogueClasscompile* THIS )
{
  return (RogueString*)(Rogue_literal_strings[94]);
}

RogueClassIOError* RogueIOError__init_object( RogueClassIOError* THIS )
{
  RogueError__init_object( ROGUE_ARG(((RogueClassError*)THIS)) );
  return (RogueClassIOError*)(THIS);
}

RogueString* RogueIOError__type_name( RogueClassIOError* THIS )
{
  return (RogueString*)(Rogue_literal_strings[110]);
}

RogueClassinstall_brew* Rogueinstall_brew__init_object( RogueClassinstall_brew* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassinstall_brew*)(THIS);
}

RogueString* Rogueinstall_brew__type_name( RogueClassinstall_brew* THIS )
{
  return (RogueString*)(Rogue_literal_strings[95]);
}

RogueClassinstall_library* Rogueinstall_library__init_object( RogueClassinstall_library* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassinstall_library*)(THIS);
}

RogueString* Rogueinstall_library__type_name( RogueClassinstall_library* THIS )
{
  return (RogueString*)(Rogue_literal_strings[96]);
}

RogueClassneed_compile* Rogueneed_compile__init_object( RogueClassneed_compile* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassneed_compile*)(THIS);
}

RogueString* Rogueneed_compile__type_name( RogueClassneed_compile* THIS )
{
  return (RogueString*)(Rogue_literal_strings[97]);
}

RogueClassmobile_or_desktop* Roguemobile_or_desktop__init_object( RogueClassmobile_or_desktop* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassmobile_or_desktop*)(THIS);
}

RogueString* Roguemobile_or_desktop__type_name( RogueClassmobile_or_desktop* THIS )
{
  return (RogueString*)(Rogue_literal_strings[98]);
}

RogueClassrequire_command_line* Roguerequire_command_line__init_object( RogueClassrequire_command_line* THIS )
{
  RogueObject__init_object( ROGUE_ARG(((RogueObject*)THIS)) );
  return (RogueClassrequire_command_line*)(THIS);
}

RogueString* Roguerequire_command_line__type_name( RogueClassrequire_command_line* THIS )
{
  return (RogueString*)(Rogue_literal_strings[99]);
}

RogueString* RogueSystemEnvironment__get__String( RogueClassSystemEnvironment THIS, RogueString* name_0 )
{
  ROGUE_DEF_LOCAL_REF(RogueString*,result_1,0);
  char* c_result = getenv( (char*)name_0->utf8 );
  if (c_result)
  {
    result_1 = RogueString_create_from_utf8( c_result );
  }

  return (RogueString*)(((((result_1))) ? (ROGUE_ARG(result_1)) : ROGUE_ARG(((RogueString*)(NULL)))));
}

RogueLogical RogueFileOptions__is_files_and_folders( RogueClassFileOptions THIS )
{
  RogueInt32 f_0 = (((THIS.flags) & (24)));
  return (RogueLogical)(((f_0 == 0) || (f_0 == 24)));
}

RogueLogical RogueFileOptions__is_files( RogueClassFileOptions THIS )
{
  return (RogueLogical)(((!!(((THIS.flags) & (8)))) || (!(!!(((THIS.flags) & (24)))))));
}

RogueLogical RogueFileOptions__is_folders( RogueClassFileOptions THIS )
{
  return (RogueLogical)(((!!(((THIS.flags) & (16)))) || (!(!!(((THIS.flags) & (24)))))));
}


void Rogue_configure( int argc, const char* argv[] )
{
  if (Rogue_configured) return;
  Rogue_configured = 1;
  
  Rogue_argc = argc;
  Rogue_argv = argv;
  
  Rogue_configure_gc();
  Rogue_configure_types();
  set_terminate( Rogue_terminate_handler );
  RogueTypeObject = &Rogue_types[ 0 ];
  RogueTypeGlobal = &Rogue_types[ 1 ];
  RogueTypePrintWriter_global_output_buffer_ = &Rogue_types[ 2 ];
  RogueTypePrintWriter = &Rogue_types[ 3 ];
  RogueTypeStringBuilder = &Rogue_types[ 4 ];
  RogueTypeByte_List = &Rogue_types[ 5 ];
  RogueTypeGenericList = &Rogue_types[ 6 ];
  RogueTypeByte = &Rogue_types[ 7 ];
  RogueTypeArray = &Rogue_types[ 9 ];
  RogueTypeInt32 = &Rogue_types[ 10 ];
  RogueTypeLogical = &Rogue_types[ 11 ];
  RogueTypeFunction___List = &Rogue_types[ 12 ];
  RogueTypeFunction__ = &Rogue_types[ 13 ];
  RogueTypeException = &Rogue_types[ 15 ];
  RogueTypeString = &Rogue_types[ 16 ];
  RogueTypeStackTrace = &Rogue_types[ 17 ];
  RogueTypeString_List = &Rogue_types[ 18 ];
  RogueTypeReal64 = &Rogue_types[ 20 ];
  RogueTypeInt64 = &Rogue_types[ 21 ];
  RogueTypeCharacter = &Rogue_types[ 22 ];
  RogueTypeCharacter_List = &Rogue_types[ 23 ];
  RogueTypeConsole = &Rogue_types[ 25 ];
  RogueTypeReader_Byte_ = &Rogue_types[ 26 ];
  RogueTypePrintWriter_output_buffer_ = &Rogue_types[ 27 ];
  RogueTypeConsoleErrorPrinter = &Rogue_types[ 28 ];
  RogueTypeConsoleIOHandler = &Rogue_types[ 29 ];
  RogueTypeMath = &Rogue_types[ 30 ];
  RogueTypeRuntime = &Rogue_types[ 31 ];
  RogueTypeFunction_190 = &Rogue_types[ 32 ];
  RogueTypeget_platform = &Rogue_types[ 33 ];
  RogueTypestandard_build = &Rogue_types[ 34 ];
  RogueTypeSystem = &Rogue_types[ 35 ];
  RogueTypeError = &Rogue_types[ 36 ];
  RogueTypeWeakReference = &Rogue_types[ 37 ];
  RogueTypeFile = &Rogue_types[ 38 ];
  RogueTypeFunction_623 = &Rogue_types[ 39 ];
  RogueTypeBlockingConsoleIOHandler = &Rogue_types[ 40 ];
  RogueTypeBuildConfig = &Rogue_types[ 41 ];
  RogueTypeinstall_emscripten = &Rogue_types[ 42 ];
  RogueTypeconfigure_build_folder = &Rogue_types[ 43 ];
  RogueTypecompile = &Rogue_types[ 44 ];
  RogueTypeIOError = &Rogue_types[ 45 ];
  RogueTypeinstall_brew = &Rogue_types[ 46 ];
  RogueTypeinstall_library = &Rogue_types[ 47 ];
  RogueTypeneed_compile = &Rogue_types[ 48 ];
  RogueTypemobile_or_desktop = &Rogue_types[ 49 ];
  RogueTyperequire_command_line = &Rogue_types[ 50 ];
  RogueTypeOptionalInt32 = &Rogue_types[ 51 ];
  RogueTypeSystemEnvironment = &Rogue_types[ 52 ];
  RogueTypeFileOptions = &Rogue_types[ 53 ];

  Rogue_literal_strings[0] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "", 0 ) ); 
  Rogue_literal_strings[1] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "null", 4 ) ); 
  Rogue_literal_strings[2] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Build/", 6 ) ); 
  Rogue_literal_strings[3] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "/Source", 7 ) ); 
  Rogue_literal_strings[4] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( ".", 1 ) ); 
  Rogue_literal_strings[5] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "/", 1 ) ); 
  Rogue_literal_strings[6] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Exception", 9 ) ); 
  Rogue_literal_strings[7] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "=", 1 ) ); 
  Rogue_literal_strings[8] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( ",", 1 ) ); 
  Rogue_literal_strings[9] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "\n", 1 ) ); 
  Rogue_literal_strings[10] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "(", 1 ) ); 
  Rogue_literal_strings[11] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Object", 6 ) ); 
  Rogue_literal_strings[12] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( " 0x", 3 ) ); 
  Rogue_literal_strings[13] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( ")", 1 ) ); 
  Rogue_literal_strings[14] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "No stack trace", 14 ) ); 
  Rogue_literal_strings[15] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Unknown", 7 ) ); 
  Rogue_literal_strings[16] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Could not get absolute path", 27 ) ); 
  Rogue_literal_strings[17] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "cpp", 3 ) ); 
  Rogue_literal_strings[18] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "macOS", 5 ) ); 
  Rogue_literal_strings[19] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "iOS", 3 ) ); 
  Rogue_literal_strings[20] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "mm", 2 ) ); 
  Rogue_literal_strings[21] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "/RogueProgram.h", 15 ) ); 
  Rogue_literal_strings[22] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "/RogueProgram.", 14 ) ); 
  Rogue_literal_strings[23] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "**", 2 ) ); 
  Rogue_literal_strings[24] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Libraries/Rogue", 15 ) ); 
  Rogue_literal_strings[25] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Source", 6 ) ); 
  Rogue_literal_strings[26] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Makefile", 8 ) ); 
  Rogue_literal_strings[27] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Build.rogue", 11 ) ); 
  Rogue_literal_strings[28] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "BuildCore.rogue", 15 ) ); 
  Rogue_literal_strings[29] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "C++", 3 ) ); 
  Rogue_literal_strings[30] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "C++,ObjC", 8 ) ); 
  Rogue_literal_strings[31] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "roguec", 6 ) ); 
  Rogue_literal_strings[32] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( " --target=", 10 ) ); 
  Rogue_literal_strings[33] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Windows", 7 ) ); 
  Rogue_literal_strings[34] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Linux", 5 ) ); 
  Rogue_literal_strings[35] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Unix", 4 ) ); 
  Rogue_literal_strings[36] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "emscripten", 10 ) ); 
  Rogue_literal_strings[37] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Desktop", 7 ) ); 
  Rogue_literal_strings[38] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Mobile", 6 ) ); 
  Rogue_literal_strings[39] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( " --gc=manual Source/Main.rogue Plasmacore --libraries=Libraries/Rogue --output=", 79 ) ); 
  Rogue_literal_strings[40] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "/RogueProgram", 13 ) ); 
  Rogue_literal_strings[41] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( " --ide", 6 ) ); 
  Rogue_literal_strings[42] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Process was not created", 23 ) ); 
  Rogue_literal_strings[43] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "help", 4 ) ); 
  Rogue_literal_strings[44] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "--ide", 5 ) ); 
  Rogue_literal_strings[45] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Android", 7 ) ); 
  Rogue_literal_strings[46] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Cygwin", 6 ) ); 
  Rogue_literal_strings[47] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "which brew >& /dev/null", 23 ) ); 
  Rogue_literal_strings[48] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "IDE", 3 ) ); 
  Rogue_literal_strings[49] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "TARGET", 6 ) ); 
  Rogue_literal_strings[50] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "/Users/sabont/PlasmacoreDemos/Game On/BuildScriptCore.rogue", 59 ) ); 
  Rogue_literal_strings[51] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( ":", 1 ) ); 
  Rogue_literal_strings[52] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "-9223372036854775808", 20 ) ); 
  Rogue_literal_strings[53] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( ": error:Run 'make ", 18 ) ); 
  Rogue_literal_strings[54] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "' from the command line to install necessary libraries.", 55 ) ); 
  Rogue_literal_strings[55] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Installing brew", 15 ) ); 
  Rogue_literal_strings[56] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "\nHomebrew must be installed.  Install now (y/n)? ", 49 ) ); 
  Rogue_literal_strings[57] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "/usr/bin/ruby -e \"$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)\"", 98 ) ); 
  Rogue_literal_strings[58] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Failed to install Homebrew.", 27 ) ); 
  Rogue_literal_strings[59] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Missing required dependency 'brew' (Homebrew).", 46 ) ); 
  Rogue_literal_strings[60] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "brew list ", 10 ) ); 
  Rogue_literal_strings[61] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( " >& /dev/null", 13 ) ); 
  Rogue_literal_strings[62] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "\nLibrary '", 10 ) ); 
  Rogue_literal_strings[63] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "' must be installed.  Install now (y/n)? ", 41 ) ); 
  Rogue_literal_strings[64] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Missing required library '", 26 ) ); 
  Rogue_literal_strings[65] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "'.", 2 ) ); 
  Rogue_literal_strings[66] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "brew install ", 13 ) ); 
  Rogue_literal_strings[67] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Failed to install library '", 27 ) ); 
  Rogue_literal_strings[68] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "emscripten installed.  Run 'emcc' and then adjust your ~/.emscripten file as\ndirected by the \"Caveats\" clause above (if present).", 129 ) ); 
  Rogue_literal_strings[69] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "USAGE\n  make [ios | macos | emscripten | linux]", 47 ) ); 
  Rogue_literal_strings[70] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "ROGUE_GC_THRESHOLD", 18 ) ); 
  Rogue_literal_strings[71] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "MB", 2 ) ); 
  Rogue_literal_strings[72] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "KB", 2 ) ); 
  Rogue_literal_strings[73] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Global", 6 ) ); 
  Rogue_literal_strings[74] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "StackTrace", 10 ) ); 
  Rogue_literal_strings[75] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "String", 6 ) ); 
  Rogue_literal_strings[76] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "GenericList", 11 ) ); 
  Rogue_literal_strings[77] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "StringBuilder", 13 ) ); 
  Rogue_literal_strings[78] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "NativeArray", 11 ) ); 
  Rogue_literal_strings[79] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Console", 7 ) ); 
  Rogue_literal_strings[80] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Math", 4 ) ); 
  Rogue_literal_strings[81] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Runtime", 7 ) ); 
  Rogue_literal_strings[82] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Function_190", 12 ) ); 
  Rogue_literal_strings[83] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "get_platform", 12 ) ); 
  Rogue_literal_strings[84] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "standard_build", 14 ) ); 
  Rogue_literal_strings[85] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "System", 6 ) ); 
  Rogue_literal_strings[86] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "WeakReference", 13 ) ); 
  Rogue_literal_strings[87] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "ConsoleErrorPrinter", 19 ) ); 
  Rogue_literal_strings[88] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "ConsoleIOHandler", 16 ) ); 
  Rogue_literal_strings[89] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "File", 4 ) ); 
  Rogue_literal_strings[90] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Function_623", 12 ) ); 
  Rogue_literal_strings[91] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "BuildConfig", 11 ) ); 
  Rogue_literal_strings[92] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "install_emscripten", 18 ) ); 
  Rogue_literal_strings[93] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "configure_build_folder", 22 ) ); 
  Rogue_literal_strings[94] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "compile", 7 ) ); 
  Rogue_literal_strings[95] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "install_brew", 12 ) ); 
  Rogue_literal_strings[96] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "install_library", 15 ) ); 
  Rogue_literal_strings[97] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "need_compile", 12 ) ); 
  Rogue_literal_strings[98] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "mobile_or_desktop", 17 ) ); 
  Rogue_literal_strings[99] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "require_command_line", 20 ) ); 
  Rogue_literal_strings[100] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Byte[]", 6 ) ); 
  Rogue_literal_strings[101] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Character[]", 11 ) ); 
  Rogue_literal_strings[102] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "String[]", 8 ) ); 
  Rogue_literal_strings[103] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Function()[]", 12 ) ); 
  Rogue_literal_strings[104] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Array<<String>>", 15 ) ); 
  Rogue_literal_strings[105] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Array<<Function()>>", 19 ) ); 
  Rogue_literal_strings[106] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Array<<Byte>>", 13 ) ); 
  Rogue_literal_strings[107] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Array<<Character>>", 18 ) ); 
  Rogue_literal_strings[108] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Error", 5 ) ); 
  Rogue_literal_strings[109] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "BlockingConsoleIOHandler", 24 ) ); 
  Rogue_literal_strings[110] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "IOError", 7 ) ); 
  Rogue_literal_strings[111] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "PrintWriter<<global_output_buffer>>", 35 ) ); 
  Rogue_literal_strings[112] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "PrintWriter", 11 ) ); 
  Rogue_literal_strings[113] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Byte", 4 ) ); 
  Rogue_literal_strings[114] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Int32", 5 ) ); 
  Rogue_literal_strings[115] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Logical", 7 ) ); 
  Rogue_literal_strings[116] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Function()", 10 ) ); 
  Rogue_literal_strings[117] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Real64", 6 ) ); 
  Rogue_literal_strings[118] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Int64", 5 ) ); 
  Rogue_literal_strings[119] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Character", 9 ) ); 
  Rogue_literal_strings[120] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Reader<<Byte>>", 14 ) ); 
  Rogue_literal_strings[121] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "PrintWriter<<output_buffer>>", 28 ) ); 
  Rogue_literal_strings[122] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "Int32?", 6 ) ); 
  Rogue_literal_strings[123] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "SystemEnvironment", 17 ) ); 
  Rogue_literal_strings[124] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "FileOptions", 11 ) ); 
  Rogue_literal_strings[125] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "console", 7 ) ); 
  Rogue_literal_strings[126] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "global_output_buffer", 20 ) ); 
  Rogue_literal_strings[127] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "exit_functions", 14 ) ); 
  Rogue_literal_strings[128] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "work_bytes", 10 ) ); 
  Rogue_literal_strings[129] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "utf8", 4 ) ); 
  Rogue_literal_strings[130] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "count", 5 ) ); 
  Rogue_literal_strings[131] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "indent", 6 ) ); 
  Rogue_literal_strings[132] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "cursor_offset", 13 ) ); 
  Rogue_literal_strings[133] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "cursor_index", 12 ) ); 
  Rogue_literal_strings[134] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "at_newline", 10 ) ); 
  Rogue_literal_strings[135] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "data", 4 ) ); 
  Rogue_literal_strings[136] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "message", 7 ) ); 
  Rogue_literal_strings[137] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "stack_trace", 11 ) ); 
  Rogue_literal_strings[138] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "entries", 7 ) ); 
  Rogue_literal_strings[139] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "is_formatted", 12 ) ); 
  Rogue_literal_strings[140] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "position", 8 ) ); 
  Rogue_literal_strings[141] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "error", 5 ) ); 
  Rogue_literal_strings[142] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "output_buffer", 13 ) ); 
  Rogue_literal_strings[143] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "input_buffer", 12 ) ); 
  Rogue_literal_strings[144] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "next_input_byte", 15 ) ); 
  Rogue_literal_strings[145] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "io_handler", 10 ) ); 
  Rogue_literal_strings[146] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "termios original_terminal_settings;", 35 ) ); 
  Rogue_literal_strings[147] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "command_line_arguments", 22 ) ); 
  Rogue_literal_strings[148] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "executable_filepath", 19 ) ); 
  Rogue_literal_strings[149] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "environment", 11 ) ); 
  Rogue_literal_strings[150] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "next_weak_reference", 19 ) ); 
  Rogue_literal_strings[151] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "RogueObject* value;", 19 ) ); 
  Rogue_literal_strings[152] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "filepath", 8 ) ); 
  Rogue_literal_strings[153] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "ide_flag", 8 ) ); 
  Rogue_literal_strings[154] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "value", 5 ) ); 
  Rogue_literal_strings[155] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "exists", 6 ) ); 
  Rogue_literal_strings[156] = (RogueString*) RogueObject_retain( RogueString_create_from_utf8( "flags", 5 ) ); 

}

void Rogue_launch()
{
  RogueStringBuilder__init_class();
  RogueRuntime__init_class();
  RogueSystem__init_class();

  RogueSystem_executable_filepath = RogueString_create_from_utf8(
      Rogue_argc ? Rogue_argv[0] : "Rogue", -1 );
  
  for (int i=1; i<Rogue_argc; ++i)
  {
    RogueString_List__add__String( RogueSystem_command_line_arguments,
        RogueString_create_from_utf8( Rogue_argv[i], -1 ) );
  }

  // Instantiate essential singletons
  ROGUE_SINGLETON( Global );

  RogueGlobal__on_launch( (RogueClassGlobal*) (RogueType_singleton(RogueTypeGlobal)) );
  Rogue_collect_garbage();
}

bool Rogue_update_tasks()
{
  // Returns true if any tasks are still active
  try
  {
    Rogue_collect_garbage();
    return false;
  }
  catch (RogueException* err)
  {
    printf( "Uncaught exception\n" );
    RogueException__display( err );
    return false;
  }
}

int main( int argc, const char* argv[] )
{
  try
  {
    Rogue_configure( argc, argv );
    Rogue_launch();

    while (Rogue_update_tasks()) {}

    Rogue_quit();
  }
  catch (RogueException* err)
  {
    printf( "Uncaught exception\n" );
    RogueException__display( err );
  }

  return 0;
}
