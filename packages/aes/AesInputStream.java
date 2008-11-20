/*  AesInputStream.c

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


import java.io.*;
import java.net.*;
import javax.crypto.*;
import javax.crypto.spec.*;
import java.security.*;
import java.security.spec.*;

public class AesInputStream extends InputStream
{
      private InputStream in;
      private Cipher cipher;
      private byte[] encrypted = new byte[16];
      private byte[] pending = new byte[15];
      private int pending_ptr = 0;
      private int pending_limit = 0;

      public AesInputStream(InputStream in, Cipher cipher)
      {
         this.in = in;
         this.cipher = cipher;
      }

      public void close() throws IOException
      {
         in.close();
      }

      public int available()
      {
         return (pending_limit - pending_ptr);
      }

      /* We don't support marking */
      public void mark(int readlimit) {}

      /* We don't support marking */
      public void reset() throws IOException
      {
         throw new IOException("Marking is not supported by AesInputStream");
      }

      /* We don't support marking */
      public boolean markSupported()
      {
         return false;
      }

      private boolean next_block() throws IOException
      {
         byte[] decrypted = null;
         if (in.read(encrypted) < 16)
            return false;
         try
         {
            decrypted = cipher.doFinal(encrypted);
         }
         catch(IllegalBlockSizeException e)
         {
            /* This SHOULD never happen, since we insist that the block is always 16 */
            e.printStackTrace();
         }
         catch(BadPaddingException b)
         {
            b.printStackTrace();
         }
         if (decrypted[0] == 0)
         {
            for (int i = 1; i < 16; i++)
               pending[i-1] = decrypted[i];
            pending_limit = 15;
         }
         else
         {
            for (int i = 1+decrypted[1]; i < 16; i++)
               pending[i-decrypted[1]-1] = decrypted[i];            
            pending_limit = 15-decrypted[1];
         }
         pending_ptr = 0;
         return true;
      }

      public int read() throws IOException
      {
         if (pending_ptr == pending_limit)
         {
            if (!next_block())
            {
               return -1;
            }
         }
         int r = pending[pending_ptr]<0?pending[pending_ptr++]+256:pending[pending_ptr++];
         return r;
      }

      public int read(byte[] buffer) throws IOException
      {
         return read(buffer, 0, buffer.length);
      }

      public int read(byte[] buffer, int s, int l) throws IOException
      {
         int read_bytes;            
         for (read_bytes = 0; read_bytes < l; read_bytes++)
         {
            int b = read();
            if(b < 0)
               return read_bytes;
            else
               buffer[read_bytes+s] = (byte)b;
         }
         return read_bytes;
      }

      public long skip(long n) throws IOException
      {
         long skipped = 0;
         for (skipped = 0; skipped < n; skipped++)
            if (read() < 0)
               break;
         return skipped;
      }


      public static void main(String[] args) throws Exception
      {         
         if (args.length < 1)
         {
            System.out.println("Usage: AesInputStream <port to listen on>");
            System.exit(0);
         }
         Cipher decrypt = Cipher.getInstance("AES/ECB/NoPadding");            
         byte[] raw = "thisisatestofaes".getBytes("ISO_8859_1");
         SecretKeySpec skeySpec = new SecretKeySpec(raw, "AES");
         decrypt.init(Cipher.DECRYPT_MODE, skeySpec);

         ServerSocket s = new ServerSocket(Integer.parseInt(args[0]), 5);
         System.out.println("Waiting for client...");
         Socket client = s.accept();         
         AesInputStream ais = new AesInputStream(client.getInputStream(), decrypt);
         while(true)
         {
            int b = ais.read();
            if (b < 0)               
               break;
            System.out.print((char)b);
         }
         System.out.println("");
         ais.close();
         client.close();
         s.close();
      }
}
