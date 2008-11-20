:-initialization(load_foreign_library(foreign(aes))).

% Write data to a memory file, show the encrypted atom, then decrypt
demo:-
  new_memory_file(MemFile),
  open_memory_file(MemFile, write, WriteStream),
  aes_encrypt_key("thisisatestofaes", EncryptContext),
  aes_open(WriteStream, EncryptContext, AesWriteStream, [close_parent(true)]),
  format(AesWriteStream, '\'This is a message which is to be encrypted\'.', []),
  close(AesWriteStream),
  memory_file_to_atom(MemFile, CipherText),
  format('Ciphertext: ~w~n', [CipherText]),

  open_memory_file(MemFile, read, ReadStream),
  aes_decrypt_key("thisisatestofaes", DecryptContext),
  aes_open(ReadStream, DecryptContext, AesReadStream, [close_parent(true)]),
  read(AesReadStream, RecoveredTerm),
  close(AesReadStream),
  format('~n~nRecovered plaintext: ~w~n', [RecoveredTerm]).

% See AesInputStream.java
transmit_to_java(Host:Port):-
  tcp_socket(S),
  tcp_connect(S, Host:Port),
  tcp_open_socket(S, Read, Write),
  aes_encrypt_key("thisisatestofaes", EncryptContext),
  aes_open(Write, EncryptContext, AesWrite, [close_parent(true)]),
  format(AesWrite, 'Hello from Prolog!', []),
  close(AesWrite),
  close(Read).

% See AesOutputStream.java
receive_from_java(Port):-
  tcp_socket(S),
  tcp_bind(S, Port),
  tcp_listen(S, 5),
  tcp_accept(S, ClientFd, Peer),
  tcp_open_socket(ClientFd, Read, Write),
  aes_decrypt_key("thisisatestofaes", EncryptContext),
  aes_open(Read, EncryptContext, AesRead, [close_parent(true)]),
  read(AesRead, Term),
  format('Message received from ~w: ~w~n', [Peer, Term]),
  close(AesRead),
  close(Write).