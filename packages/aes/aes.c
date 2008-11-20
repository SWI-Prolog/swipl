/*  aes.c

    Author:        Matt Lilley
    E-mail:        matt.lilley@securitease.com
    WWW:           http://www.securitease.com
    Copyright (C): 2005-2008, SecuritEase

    This library is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public
    License as published by the Free Software Foundation; either
    version 2.1 of the License, or (at your option) any later version.

    This library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

#ifdef WIN32
#include <windows.h>
#endif

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <aes.h>
#include <SWI-Stream.h>
#include <SWI-Prolog.h>

PL_blob_t aes_ctx_blob_t;
static atom_t ATOM_close_parent;	/* close_parent(Bool) */
static functor_t FUNCTOR_error2;	/* error(Formal, Context) */
static functor_t FUNCTOR_type_error2;	/* type_error(Term, Expected) */

static int type_error(term_t actual, const char *expected)
{
   term_t ex = PL_new_term_ref();
   PL_unify_term(ex, PL_FUNCTOR, FUNCTOR_error2,
                 PL_FUNCTOR, FUNCTOR_type_error2,
                 PL_CHARS, expected,
                 PL_TERM, actual,
                 PL_VARIABLE);   
   return PL_raise_exception(ex);
}


#define BLOCK_LEN 16

#define COPY_FLAGS (SIO_INPUT|SIO_OUTPUT| \
		    SIO_TEXT| \
		    SIO_REPXML|SIO_REPPL|\
		    SIO_RECORDPOS)


static int debuglevel = 0;
static int aes_gc = 1;
#define DEBUG(n, g) if ( debuglevel >= n ) g

functor_t FUNCTOR_aes_encrypt_ctx;
functor_t FUNCTOR_aes_decrypt_ctx;

/* 
 * Export DLL functions
 */
install_t install();
foreign_t aes_encrypt_key_pl(term_t key_t, term_t aes_encrypt_ctx_t);
foreign_t aes_encrypt_pl(term_t aes_encrypt_ctx_t, term_t in_t, term_t out_t);
foreign_t aes_decrypt_key_pl(term_t key_t, term_t aes_decrypt_ctx_t);
foreign_t aes_open(term_t original, term_t ctx, term_t new, term_t options);

typedef struct
{
      void* aes_ctx;
      IOSTREAM* stream;
      int out_count;
      atom_t key_handle;
      int close_parent;
      struct
      {
            unsigned char header;
            unsigned char buffer[15];
      } pending_packet;
} aes_stream;

static ssize_t aesread(void* handle, char* buf, size_t size)
{
   unsigned char decrypted_block[17];
   unsigned char encrypted_block[17];
   unsigned char* in;
   aes_stream* stream_ctx = handle;
   int encrypted_bytes_available;
   int readlength = 0;
   int startbyte;
   int can_read_more = 1;
   int out_ptr = 0;
   
   /* We can make use of the buffer already available in the parent stream */
   encrypted_bytes_available = (long)(stream_ctx->stream->limitp - stream_ctx->stream->bufp);
   DEBUG(2, Sdprintf("AES Read requested\n"));
   while(can_read_more)
   {
      can_read_more = 0;
      /* provided it contains at least one block, use the existing data */
      if (encrypted_bytes_available >= 16)
      {
         in = (unsigned char*)stream_ctx->stream->bufp;
         /* We must adjust the buffer since we've 'consumed' the data */
         stream_ctx->stream->bufp+=16;
         if (encrypted_bytes_available >= 32)
         {
            DEBUG(2, Sdprintf("More data will be available after this reading!\n"));
            can_read_more = 0;
         }
         else
            DEBUG(2, Sdprintf("NO data will be available after this reading!\n"));
      }
      else
      {
         /* Otherwise, we need to read some more bytes */
         if (Sfeof(stream_ctx->stream))
         {
            /* This is an EOF. We just return 0 as the number of bytes read - is that right? */
            DEBUG(2, Sdprintf("Unexpected EOF?\n"));
            return 0;
         }
         else
         {
            /* Note that Sfread reads data from the buffer if it is available, so we don't have
               to worry about a partial packet which was already in the buffer */
            int p = 0;
            /* Note that Sfread may not return 16 bytes on a single read */
            while(p < 16)
            {
               int r = 0;
               DEBUG(2, Sdprintf("Must call Sfread\n"));
               if ((r = Sfread((char*)&encrypted_block[p], sizeof(char), 16-p, stream_ctx->stream)) > 0)
               {
                  /* Successfully read 16 bytes from the stream */
                  DEBUG(2, Sdprintf("Read 16 bytes from stream\n"));
                  in = &encrypted_block[0];
               }
               else
               {
                  /* Failed to read 16 bytes from the stream... unexpected EOF? */
                  DEBUG(2, Sdprintf("Critical failure - Unexpected EOF\n"));
                  return 0;
               }
               p+=r;
            }
         }
      }
      /* Now we decrypt the bytes */
      aes_decrypt(in, &decrypted_block[0], (aes_decrypt_ctx*)stream_ctx->aes_ctx);
      /* TODO: What if we read more than there is space to fit? Need to check size_t! */
      
      if (decrypted_block[0] == 1)
      {
         /* This block contains padding. The first byte indicates the length */
         unsigned int padlength = decrypted_block[1];
         DEBUG(2, Sdprintf("This block contains padding: %d bytes\n", padlength));
         /* Therefore we can determine how many real bytes there are and where they start */
         startbyte = 1+padlength;
         readlength += 16-startbyte;
         DEBUG(2, Sdprintf("Copying %d bytes to the buffer from %d\n", readlength, startbyte));
         /* Read just the real bytes */
         memcpy(&buf[out_ptr], &decrypted_block[startbyte], readlength);
      }
      else if (decrypted_block[0] == 0)
      {
         DEBUG(2, Sdprintf("This block contains only data\n"));
         /* Bytes from 1-15 are real. Just the one header byte to discard */
         startbyte = 1;
         readlength += 15;
         DEBUG(2, Sdprintf("Copying %d bytes to the buffer from %d\n", readlength, startbyte));
         memcpy(&buf[out_ptr], &decrypted_block[startbyte], readlength);
      }
      else
      {
         /* Decode failure! */
         /* TODO: I don't think this actually works */
         term_t exception = PL_new_term_ref();
         Sdprintf("DECODE FAILURE!\n");
         PL_free(stream_ctx);
         PL_unify_term(exception,
                       PL_FUNCTOR, PL_new_functor(PL_new_atom("aes_error"), 1),
                       PL_CHARS, "decryption_failure");
         PL_raise_exception(exception);
         return 0;
      }
      out_ptr+=readlength;
   }
   return readlength;
}

static int aesflush(aes_stream* stream_ctx)
{
   unsigned char encrypted[16];
   unsigned char plain[16];
   int rc;

   /* How many bytes are we going to try and write? */
   int written_bytes = stream_ctx->out_count;   

   DEBUG(3, Sdprintf("Flush requested on %d bytes\n", written_bytes));   
   if (stream_ctx->out_count == 0)
   {
      /* Nothing to do! */
      DEBUG(3, Sdprintf("No bytes to flush\n"));
      return 0;
   }
   else if (stream_ctx->out_count == 15)
   {
      /* Full buffer, no padding required */
      DEBUG(4, Sdprintf("Full buffer to flush\n"));
      stream_ctx->pending_packet.header = 0;
      /* Do the encryption */
      DEBUG(4, Sdprintf("Encrypting packet\n"));
      aes_encrypt((unsigned char*)&(stream_ctx->pending_packet), encrypted, stream_ctx->aes_ctx);
      DEBUG(4, Sdprintf("Writing 16 encrypted bytes to stream\n"));
      Sfwrite(encrypted, sizeof(char), 16, stream_ctx->stream);
   }
   else
   {
      /* Padding required */
      DEBUG(4, Sdprintf("Padding packet. Only %d bytes available\n", stream_ctx->out_count));
      memset(&plain[0], 0, 16);
      memcpy(&plain[16-stream_ctx->out_count], stream_ctx->pending_packet.buffer, stream_ctx->out_count);
      plain[0] = 1; /* Includes padding */
      plain[1] = (15-stream_ctx->out_count); /* Length of padding */
      /* Do the encryption */
      DEBUG(4, Sdprintf("Encrypting packet\n"));
      aes_encrypt(&plain[0], encrypted, stream_ctx->aes_ctx);
      DEBUG(4, Sdprintf("Writing 16 encrypted bytes to stream\n"));
      Sfwrite(encrypted, sizeof(char), 16, stream_ctx->stream);      
   }
   stream_ctx->out_count = 0;
   DEBUG(3, Sdprintf("wrote %d bytes to parent\n", written_bytes));   
   DEBUG(3, Sdprintf("Flushing parent\n"));  
   rc = Sflush(stream_ctx->stream);
   DEBUG(3, Sdprintf("Flush result: %d\n", rc));
   return written_bytes;
}

static ssize_t aeswrite(void* handle, char* buf, size_t size)
{
   /* This is quite complicated. We have to continue to accumulate
      data until we have 15 bytes, at which point we can encrypt them,
      prepending a 0 to indicate 'no padding'.

      If we must flush before we have 15 bytes, then we add a 1, then the
      requisite padding, then the actual payload, and encrypt that.

      When padding remember that the pad indicator will provide 1 byte of
      padding
   */      
   aes_stream* stream_ctx = handle;
   int j;
   DEBUG(4, Sdprintf("Writing %d bytes to stream. out_count is %d\n", size, stream_ctx->out_count));
   for (j = 0; j < size; )
   {
      if ((stream_ctx->out_count) == 15)
      {
         DEBUG(4, Sdprintf("Write triggered flush...\n"));
         aesflush(stream_ctx);
      }
      DEBUG(4, Sdprintf("writing to buffer. out_count is %d\n", stream_ctx->out_count));
      stream_ctx->pending_packet.buffer[stream_ctx->out_count++] = buf[j++];
   }
   return j;
}

static int aesclose(void *handle)
{
   aes_stream* stream_ctx = handle;
   int result2 = 0;
   int result = 0;
   if (stream_ctx->stream->flags & SIO_OUTPUT)
   {
      DEBUG(2, Sdprintf("Closing, so flushing parent\n"));
      result2 = aesflush(stream_ctx);
      DEBUG(2, Sdprintf("Result of flushing: %d\n", result2));      
   }
   if ( stream_ctx->stream->upstream )
   {
      DEBUG(2, Sdprintf("Defiltering\n"));
      Sset_filter(stream_ctx->stream, NULL);
   }
   else
   {
      DEBUG(2, Sdprintf("Releasing parent stream\n"));
      PL_release_stream(stream_ctx->stream);
   }
   if (stream_ctx->close_parent)
   {
      result = Sclose(stream_ctx->stream);
      DEBUG(2, Sdprintf("Result of closing parent stream: %d\n", result));         
   }
   else
      result = 1;
   DEBUG(1, Sdprintf("Unregistering atom %x\n", stream_ctx->key_handle));
   PL_unregister_atom(stream_ctx->key_handle);
   if (result == 0 && result2 != 0)
   {
      result = result2;
   }
   PL_free(stream_ctx);
   return result;
}



static int aescontrol(void *handle, int op, void *data)
{
   aes_stream* stream_ctx = handle;
   switch(op)
   {
      case SIO_FLUSHOUTPUT:         
         DEBUG(2, Sdprintf("Flushing output\n"));
         return aesflush(stream_ctx);
      case SIO_SETENCODING:
         /* All Jan's implementations return 0 here, so I guess we should too! */
         return 0;				
      default:
         /* Pass the control to the parent stream, if possible */
         if (stream_ctx->stream->functions->control)
         {
            return (*stream_ctx->stream->functions->control)(stream_ctx->stream->handle, op, data);
         }
         /* Failed to handle -> return -1 */
         return -1;
   }
}

static IOFUNCTIONS aesfunctions =
{ aesread,
  aeswrite,
  NULL,					/* seek */
  aesclose,
  aescontrol,				/* zcontrol */
  NULL,					/* seek64 */
};

static int get_bool_ex(term_t t, int *i)
{
   if ( PL_get_bool(t, i) )
      return TRUE;
   return type_error(t, "boolean");
}


foreign_t aes_open(term_t original, term_t key_ctx, term_t new, term_t options)
{
   term_t exception;
   term_t key_ctx_ptr = PL_new_term_ref();
   term_t tail = PL_copy_term_ref(options);
   term_t head = PL_new_term_ref();
   int close_parent = FALSE;
   IOSTREAM *s, *s2;
   aes_stream* stream_ctx;

   while(PL_get_list(tail, head, tail))
   {
      atom_t name;
      int arity;
      term_t arg = PL_new_term_ref();

      if ( !PL_get_name_arity(head, &name, &arity) || arity != 1 )
         return type_error(head, "option");
      PL_get_arg(1, head, arg);

      if ( name == ATOM_close_parent )
      {
         if ( !get_bool_ex(arg, &close_parent) )
            return FALSE;
      }
   }
   if ( !PL_get_nil(tail) )
      return type_error(tail, "list");

   
   /* Firstly, get the stream out of the first argument */
   if (!PL_get_stream_handle(original, &s))
   {
      exception = PL_new_term_ref();
      PL_unify_term(exception,
                    PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                    PL_CHARS, "stream",
                    PL_TERM, original);
      return PL_raise_exception(exception);
   }

   /* Next, let's allocate a space for our control object */
   stream_ctx = PL_malloc(sizeof(aes_stream));
   stream_ctx->stream = s;
   stream_ctx->out_count = 0;
   stream_ctx->close_parent = close_parent;
   if (s->flags & SIO_INPUT)
   {
      /* If it's an input then we'll have a decrypt_ctx */
      if (!(PL_unify_term(key_ctx,
                          PL_FUNCTOR, FUNCTOR_aes_decrypt_ctx,
                          PL_TERM, key_ctx_ptr)))
      {
         exception = PL_new_term_ref();
         PL_free(stream_ctx);
         PL_unify_term(exception,
                       PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                       PL_CHARS, "aes_decrypt_ctx",
                       PL_TERM, key_ctx);
         return PL_raise_exception(exception);
      }
   }  
   else if (s->flags & SIO_OUTPUT)
   {
      /* If it's an output then we'll have a encrypt_ctx */
      if (!(PL_unify_term(key_ctx, PL_FUNCTOR, FUNCTOR_aes_encrypt_ctx,
                          PL_TERM, key_ctx_ptr)))
      {
         exception = PL_new_term_ref();
         PL_free(stream_ctx);
         PL_unify_term(exception,
                       PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                       PL_CHARS, "aes_encrypt_ctx",
                       PL_TERM, key_ctx);
         return PL_raise_exception(exception);
      }
   }
   else
   {
      /* If it's neither then panic */
      exception = PL_new_term_ref();
      PL_free(stream_ctx);
      PL_unify_term(exception,
                    PL_FUNCTOR, PL_new_functor(PL_new_atom("io_error"), 2),
                    PL_CHARS, "neither_input_nor_output",
                    PL_TERM, original);
      return PL_raise_exception(exception);
   }

   /* Next we get unpack the key */
   if (!PL_get_blob(key_ctx_ptr, (void*)&stream_ctx->aes_ctx, NULL, NULL))
   {
      exception = PL_new_term_ref();
      PL_free(stream_ctx);
      PL_unify_term(exception,
                    PL_FUNCTOR, PL_new_functor(PL_new_atom("aes_error"), 2),
                    PL_CHARS, "unable_to_retrieve_key",
                    PL_TERM, key_ctx_ptr);
      return PL_raise_exception(exception);
   }
   PL_get_atom(key_ctx_ptr, &stream_ctx->key_handle);
   PL_register_atom(stream_ctx->key_handle);
   DEBUG(1, Sdprintf("registering atom %x\n", stream_ctx->key_handle));
   /* Create the child stream. Note that we don't transmit/receive any headers -
      that is all taken care of at the application layer */
   if (!(s2 = Snew(stream_ctx,
                   (s->flags&COPY_FLAGS)|SIO_FBUF,
                   &aesfunctions)))
   {
      PL_free(stream_ctx);
      PL_fail;
   }

   /* Indicate we are filtering this stream */
   Sset_filter(s, s2);

   /* Release our handle to the parent. Note that this does NOT close the parent */
   PL_release_stream(s);

   /* Finally, return the new stream */
   if (!PL_unify_stream(new, s2))
   {
      Sclose(s2);
      exception = PL_new_term_ref();
      PL_unify_term(exception,
                    PL_FUNCTOR, PL_new_functor(PL_new_atom("instantiation_error"), 1),
                    PL_TERM, new);
      return PL_raise_exception(exception);
   }
   DEBUG(2, Sdprintf("Successfully opened aes stream\n"));
   PL_succeed;
}

/*
 * aes_encrypt_key_pl
 */
foreign_t aes_encrypt_key_pl(term_t key_t,
                             term_t aes_encrypt_ctx_t)
  {
  char *key;
  size_t key_len;
  aes_encrypt_ctx *ctx;
  term_t wrapper = PL_new_term_ref();

  
  if(!(PL_get_list_nchars(key_t, &key_len, &key, BUF_RING) &&
       (key_len == 16 || key_len == 24 || key_len == 32)))
		{
    term_t except = PL_new_term_ref();

    PL_unify_term(except,
                  PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                  PL_CHARS, "list of exactly 16, 24 or 32 char codes expected",
                  PL_TERM, key_t);

    return PL_raise_exception(except);    
    }

  ctx = PL_malloc(sizeof(aes_encrypt_ctx));

  aes_encrypt_key((unsigned char*) key, key_len, ctx);
  PL_put_blob(wrapper, ctx, sizeof(void*), &aes_ctx_blob_t);
  DEBUG(1, Sdprintf("Creating aes encrypt context at %x\n", ctx));  
  return PL_unify_term(aes_encrypt_ctx_t,
                       PL_FUNCTOR, PL_new_functor(PL_new_atom("aes_encrypt_ctx"), 1),
                       PL_TERM, wrapper);
  }


/*
 * aes_encrypt_pl
 */
foreign_t aes_encrypt_pl(term_t aes_encrypt_ctx_t,
                         term_t in_t,
                         term_t out_t)
  {
  atom_t name;
  int arity;
  term_t wrapper = PL_new_term_ref();
  aes_encrypt_ctx *ctx;
  size_t in_len;
  char *in, out[BLOCK_LEN];
  
  if(!(PL_get_name_arity(aes_encrypt_ctx_t, &name, &arity) &&
       strcmp(PL_atom_chars(name), "aes_encrypt_ctx") == 0 &&
       arity == 1                                          &&
       PL_get_arg(1, aes_encrypt_ctx_t, wrapper)           &&
       PL_get_blob(wrapper, (void*)&ctx, NULL, NULL)))
    {
    term_t except = PL_new_term_ref();

    PL_unify_term(except,
                  PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                  PL_CHARS, "aes_encrypt_ctx/1 term expected",
                  PL_TERM, aes_encrypt_ctx_t);

    return PL_raise_exception(except);    
    }
  
  if(!(PL_get_list_nchars(in_t, &in_len, &in, BUF_RING) &&
       in_len == BLOCK_LEN))
		{
    term_t except = PL_new_term_ref();

    PL_unify_term(except,
                  PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                  PL_CHARS, "list of exactly 16 char codes expected",
                  PL_TERM, in_t);

    return PL_raise_exception(except);    
    }
  
  aes_encrypt((unsigned char*) in, (unsigned char*) out, ctx);
          
  return PL_unify_list_ncodes(out_t, BLOCK_LEN, out);
  }


/*
 * aes_decrypt_key_pl
 */
foreign_t aes_decrypt_key_pl(term_t key_t,
                             term_t aes_decrypt_ctx_t)
  {
  char *key;
  size_t key_len;
  aes_decrypt_ctx *ctx;
  term_t wrapper = PL_new_term_ref();
  
  if(!(PL_get_list_nchars(key_t, &key_len, &key, BUF_RING) &&
       (key_len == 16 || key_len == 24 || key_len == 32)))
		{
    term_t except = PL_new_term_ref();

    PL_unify_term(except,
                  PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                  PL_CHARS, "list of exactly 16, 24 or 32 char codes expected",
                  PL_TERM, key_t);

    return PL_raise_exception(except);    
    }


  ctx = PL_malloc(sizeof(aes_decrypt_ctx));

  aes_decrypt_key((unsigned char*) key, key_len, ctx);  
  PL_put_blob(wrapper, ctx, sizeof(void*), &aes_ctx_blob_t);
  DEBUG(1, Sdprintf("Creating aes decrypt context at %x\n", ctx));  
  
  return PL_unify_term(aes_decrypt_ctx_t,
                       PL_FUNCTOR, PL_new_functor(PL_new_atom("aes_decrypt_ctx"), 1),
                       PL_TERM, wrapper);
  }


/*
 * aes_decrypt_pl
 */
foreign_t aes_decrypt_pl(term_t aes_decrypt_ctx_t,
                         term_t in_t,
                         term_t out_t)
  {
  atom_t name;
  int arity;
  term_t wrapper = PL_new_term_ref();
  aes_decrypt_ctx *ctx;
  size_t in_len;
  char *in, out[BLOCK_LEN];
  
  if(!(PL_get_name_arity(aes_decrypt_ctx_t, &name, &arity) &&
       strcmp(PL_atom_chars(name), "aes_decrypt_ctx") == 0 &&
       arity == 1                                          &&
       PL_get_arg(1, aes_decrypt_ctx_t, wrapper)           &&
       PL_get_blob(wrapper, (void*)&ctx, NULL, NULL)))
    {
    term_t except = PL_new_term_ref();

    PL_unify_term(except,
                  PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                  PL_CHARS, "aes_decrypt_ctx/1 term expected",
                  PL_TERM, aes_decrypt_ctx_t);

    return PL_raise_exception(except);    
    }

  if(!(PL_get_list_nchars(in_t, &in_len, &in, BUF_RING) &&
       in_len == BLOCK_LEN))
		{
    term_t except = PL_new_term_ref();

    PL_unify_term(except,
                  PL_FUNCTOR, PL_new_functor(PL_new_atom("type_error"), 2),
                  PL_CHARS, "list of exactly 16 char codes expected",
                  PL_TERM, in_t);

    return PL_raise_exception(except);    
    }
  
  aes_decrypt((unsigned char*) in, (unsigned char*) out, ctx);
  
  return PL_unify_list_ncodes(out_t, BLOCK_LEN, out);
  }



static foreign_t aes_debug(term_t level)
{
   return PL_get_integer(level, &debuglevel);
}

static foreign_t aes_gc_flag(term_t value)
{
   return PL_get_integer(value, &aes_gc);
}


int release_aes_context(atom_t atom)
{
   void * underlying;
   size_t l;
   if (aes_gc == 0)
      return TRUE;
   underlying = PL_blob_data(atom, &l, NULL);
   DEBUG(1, Sdprintf("Releasing aes context at %x\n", underlying));
   PL_free(underlying);
   DEBUG(1, Sdprintf("Released\n"));
   return TRUE;   
}

install_t install()
  {
  PL_register_foreign("aes_encrypt_key", 2, aes_encrypt_key_pl, 0);
  PL_register_foreign("aes_encrypt",     3, aes_encrypt_pl,     0);
  PL_register_foreign("aes_decrypt_key", 2, aes_decrypt_key_pl, 0);
  PL_register_foreign("aes_decrypt",     3, aes_decrypt_pl,     0);
  PL_register_foreign("aes_open",        4, aes_open,           0);
  PL_register_foreign("aes_debug",       1, aes_debug,          0);
  PL_register_foreign("aes_gc_flag",     1, aes_gc_flag,        0);
  FUNCTOR_aes_decrypt_ctx = PL_new_functor(PL_new_atom("aes_decrypt_ctx"), 1);
  FUNCTOR_aes_encrypt_ctx = PL_new_functor(PL_new_atom("aes_encrypt_ctx"), 1);
  FUNCTOR_error2 = PL_new_functor(PL_new_atom("error"), 2);
  FUNCTOR_type_error2= PL_new_functor(PL_new_atom("type_error"), 2);
   
  ATOM_close_parent = PL_new_atom("close_parent");
  memset(&aes_ctx_blob_t, 0, sizeof(aes_ctx_blob_t));
  aes_ctx_blob_t.magic = PL_BLOB_MAGIC;
  aes_ctx_blob_t.flags = PL_BLOB_UNIQUE | PL_BLOB_NOCOPY;
  aes_ctx_blob_t.name = "AES Context";
  aes_ctx_blob_t.release = release_aes_context;     
  }
