/*  AesOutputStream.java

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

public class AesOutputStream extends OutputStream
{
      private OutputStream out;
      private Cipher cipher;
      private byte[] pending = new byte[15];
      private byte[] assembly = new byte[16];
      private int pending_ptr = 0;

      public AesOutputStream(OutputStream out, Cipher cipher) throws IOException
      {
         this.out = out;
         this.cipher = cipher;
      }

      public void close() throws IOException
      {
         flush();
         out.close();
      }

      public void flush() throws IOException
      {
         aesflush(true);
      }

      public void aesflush(boolean forceFlush) throws IOException
      {
         if (pending_ptr == 0)
         {
            if (forceFlush)
            {
               out.flush();
            }
            return; /* Nothing to do */
         }
         else if (pending_ptr == 15)
         {
            /* Full buffer */
            assembly[0] = 0;
            for (int i = 0; i < 15; i++)
            {
               assembly[i+1] = pending[i];
            }
         }
         else
         {
            assembly[0] = 1;
            assembly[1] = (byte)(15-pending_ptr);
            for (int i = 2; i < 16-pending_ptr; i++)
               assembly[i] = 0;
            for (int i = 16-pending_ptr; i < 16; i++)
               assembly[i] = pending[i - 16 + pending_ptr];
         }
         try
         {
            out.write(cipher.doFinal(assembly));
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
         if (forceFlush)
         {
            out.flush();                  
         }
         pending_ptr = 0;
      }

      public void write(byte[] b) throws IOException
      {
         write(b, 0, b.length);
      }

      public void write(byte[] b, int s, int l) throws IOException
      {
         for(int i = 0; i < l; i++)
         {
            if (pending_ptr == 15)
               aesflush(false);
            pending[pending_ptr++] = b[s+i];
         }
      }

      public void write(int b) throws IOException
      {
         if (pending_ptr == 15)
            aesflush(false);
         pending[pending_ptr++] = (byte)b;
      }


      /* tests */
      public static void main(String[] args) throws Exception
      {
        if (args.length < 2)
         {
            System.out.println("Usage: AesOutputStream <host to connect to> <port to connect on>");
            System.exit(0);
         }
         Cipher encrypt = Cipher.getInstance("AES/ECB/NoPadding");            
         byte[] raw = "thisisatestofaes".getBytes("ISO_8859_1");
         SecretKeySpec skeySpec = new SecretKeySpec(raw, "AES");
         encrypt.init(Cipher.ENCRYPT_MODE, skeySpec);

         Socket s = new Socket(args[0], Integer.parseInt(args[1]));
         AesOutputStream aos = new AesOutputStream(s.getOutputStream(), encrypt);
         aos.write("'Hello from Java!'.".getBytes("ISO_8859_1"));
         aos.close();
         s.close();
      }
}
