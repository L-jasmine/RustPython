use crate::vm::{PyObjectRef, VirtualMachine};
#[cfg(feature = "ssl")]
pub(super) use _socket::{sock_select, timeout_error_msg, PySocket, SelectKind};

pub fn make_module(vm: &VirtualMachine) -> PyObjectRef {
    _socket::make_module(vm)
}

mod wasmedge_sock {
    use std::ffi::CString;
    use std::io;
    use std::io::{Read, Write};
    use std::net::{
        IpAddr, Ipv4Addr, Ipv6Addr, Shutdown, SocketAddr, SocketAddrV4, SocketAddrV6, ToSocketAddrs,
    };
    use std::os::wasi::prelude::{AsRawFd, RawFd};

    #[derive(Copy, Clone)]
    #[repr(u8)]
    pub enum SocketType {
        Datagram,
        Stream,
    }

    #[derive(Copy, Clone)]
    #[repr(u8)]
    pub enum AddressFamily {
        Inet4,
    }

    #[repr(C)]
    pub struct WasiAddress {
        pub buf: *const u8,
        pub size: usize,
    }

    #[repr(C)]
    pub struct IovecRead {
        pub buf: *mut u8,
        pub size: usize,
    }

    #[repr(C)]
    pub struct IovecWrite {
        pub buf: *const u8,
        pub size: usize,
    }

    pub type RawSocket = RawFd;

    #[derive(Debug)]
    pub struct Socket(pub RawSocket);

    impl Drop for Socket {
        fn drop(&mut self) {
            self.shutdown(Shutdown::Both);
        }
    }

    impl AsRawFd for Socket {
        fn as_raw_fd(&self) -> RawFd {
            self.0
        }
    }

    macro_rules! syscall {
        ($fn: ident ( $($arg: expr),* $(,)* ) ) => {{
            #[allow(unused_unsafe)]
            let res = unsafe { libc::$fn($($arg, )*) };
            if res == -1 {
                Err(std::io::Error::last_os_error())
            } else {
                Ok(res)
            }
        }};
    }

    fn fcntl_add(fd: RawFd, get_cmd: i32, set_cmd: i32, flag: i32) -> io::Result<()> {
        let previous = syscall!(fcntl(fd, get_cmd))?;
        let new = previous | flag;
        if new != previous {
            syscall!(fcntl(fd, set_cmd, new)).map(|_| ())
        } else {
            // Flag was already set.
            Ok(())
        }
    }

    /// Remove `flag` to the current set flags of `F_GETFD`.
    fn fcntl_remove(fd: RawFd, get_cmd: i32, set_cmd: i32, flag: i32) -> io::Result<()> {
        let previous = syscall!(fcntl(fd, get_cmd))?;
        let new = previous & !flag;
        if new != previous {
            syscall!(fcntl(fd, set_cmd, new)).map(|_| ())
        } else {
            // Flag was already set.
            Ok(())
        }
    }

    impl Socket {
        pub fn new(_addr_family: i32, sock_kind: i32) -> io::Result<Self> {
            unsafe {
                if sock_kind != super::socket_types::SOCK_STREAM {
                    Err(io::Error::from(io::ErrorKind::Unsupported))?;
                }
                let sock_type = SocketType::Stream;
                let mut fd = 0;
                let res = sock_open(AddressFamily::Inet4 as u8, sock_type as u8, &mut fd);
                if res == 0 {
                    Ok(Socket(fd as i32))
                } else {
                    Err(io::Error::from_raw_os_error(res as i32))
                }
            }
        }

        pub fn send(&self, buf: &[u8]) -> io::Result<usize> {
            unsafe {
                let mut send_len: u32 = 0;
                let vec = IovecWrite {
                    buf: buf.as_ptr(),
                    size: buf.len(),
                };
                let res = sock_send(self.as_raw_fd() as u32, &vec, 1, 0, &mut send_len);
                if res == 0 {
                    Ok(send_len as usize)
                } else {
                    Err(io::Error::from_raw_os_error(res as i32))
                }
            }
        }
        pub fn recv(&self, buf: &mut [u8]) -> io::Result<usize> {
            let flags = 0;
            let mut recv_len: usize = 0;
            let mut oflags: usize = 0;
            let mut vec = IovecRead {
                buf: buf.as_mut_ptr(),
                size: buf.len(),
            };

            unsafe {
                let res = sock_recv(
                    self.as_raw_fd() as u32,
                    &mut vec,
                    1,
                    flags,
                    &mut recv_len,
                    &mut oflags,
                );
                if res == 0 {
                    Ok(recv_len)
                } else {
                    Err(io::Error::from_raw_os_error(res as i32))
                }
            }
        }

        pub fn set_nonblocking(&self, nonblocking: bool) -> io::Result<()> {
            let fd = self.as_raw_fd();
            if nonblocking {
                fcntl_add(fd, libc::F_GETFL, libc::F_SETFL, libc::O_NONBLOCK)
            } else {
                fcntl_remove(fd, libc::F_GETFL, libc::F_SETFL, libc::O_NONBLOCK)
            }
        }

        pub fn connect(&self, addrs: &SocketAddr) -> io::Result<()> {
            let mut fd = self.as_raw_fd();
            let mut vaddr: [u8; 4] = [0; 4];
            let mut port: u16 = 0;
            if let SocketAddr::V4(addrs) = addrs {
                vaddr = addrs.ip().octets();
                port = addrs.port();
            }
            let mut addr = WasiAddress {
                buf: vaddr.as_ptr(),
                size: 4,
            };

            unsafe {
                let res = sock_connect(fd as u32, &mut addr, port as u32);
                if res != 0 {
                    Err(io::Error::from_raw_os_error(res as i32))
                } else {
                    Ok(())
                }
            }
        }

        pub fn bind(&self, addrs: &SocketAddr) -> io::Result<()> {
            unsafe {
                let fd = self.as_raw_fd();
                let mut vaddr: [u8; 16] = [0; 16];
                let mut port: u16 = 0;
                let mut size = 0;
                match addrs {
                    SocketAddr::V4(addr) => {
                        let ip = addr.ip().octets();
                        (&mut vaddr[0..4]).clone_from_slice(&ip);
                        port = addr.port();
                        size = 4;
                    }
                    SocketAddr::V6(addr) => {
                        let ip = addr.ip().octets();
                        vaddr.clone_from_slice(&ip);
                        port = addr.port();
                        size = 16;
                    }
                }
                let mut addr = WasiAddress {
                    buf: vaddr.as_ptr(),
                    size,
                };
                let res = sock_bind(fd as u32, &mut addr, port as u32);
                if res != 0 {
                    Err(io::Error::from_raw_os_error(res as i32))
                } else {
                    Ok(())
                }
            }
        }

        pub fn listen(&self, backlog: i32) -> io::Result<()> {
            unsafe {
                let fd = self.as_raw_fd();
                let res = sock_listen(fd as u32, backlog as u32);
                if res != 0 {
                    Err(io::Error::from_raw_os_error(res as i32))
                } else {
                    Ok(())
                }
            }
        }

        pub fn accept(&self) -> io::Result<Self> {
            unsafe {
                let mut fd: u32 = 0;
                let res = sock_accept(self.as_raw_fd() as u32, &mut fd);
                if res != 0 {
                    Err(io::Error::from_raw_os_error(res as i32))
                } else {
                    Ok(Socket(fd as i32))
                }
            }
        }

        pub fn get_local(&self) -> io::Result<SocketAddr> {
            unsafe {
                let fd = self.0;
                let addr_buf = [0u8; 16];
                let mut addr = WasiAddress {
                    buf: addr_buf.as_ptr(),
                    size: 16,
                };
                let mut addr_type = 0;
                let mut port = 0;
                let res = sock_get_local(fd as u32, &mut addr, &mut addr_type, &mut port);
                if res != 0 {
                    Err(io::Error::from_raw_os_error(res as i32))
                } else {
                    if addr_type == 4 {
                        let ip_addr =
                            Ipv4Addr::new(addr_buf[0], addr_buf[1], addr_buf[2], addr_buf[3]);
                        Ok(SocketAddr::V4(SocketAddrV4::new(ip_addr, port as u16)))
                    } else if addr_type == 6 {
                        let ip_addr = Ipv6Addr::from(addr_buf);
                        Ok(SocketAddr::V6(SocketAddrV6::new(
                            ip_addr,
                            port as u16,
                            0,
                            0,
                        )))
                    } else {
                        Err(io::Error::from(io::ErrorKind::Unsupported))
                    }
                }
            }
        }

        pub fn get_peer(&self) -> io::Result<SocketAddr> {
            unsafe {
                let fd = self.0;
                let addr_buf = [0u8; 16];
                let mut addr = WasiAddress {
                    buf: addr_buf.as_ptr(),
                    size: 16,
                };
                let mut addr_type = 0;
                let mut port = 0;
                let res = sock_get_peer(fd as u32, &mut addr, &mut addr_type, &mut port);
                if res != 0 {
                    Err(io::Error::from_raw_os_error(res as i32))
                } else {
                    if addr_type == 4 {
                        let ip_addr =
                            Ipv4Addr::new(addr_buf[0], addr_buf[1], addr_buf[2], addr_buf[3]);
                        Ok(SocketAddr::V4(SocketAddrV4::new(ip_addr, port as u16)))
                    } else if addr_type == 6 {
                        let ip_addr = Ipv6Addr::from(addr_buf);
                        Ok(SocketAddr::V6(SocketAddrV6::new(
                            ip_addr,
                            port as u16,
                            0,
                            0,
                        )))
                    } else {
                        Err(io::Error::from(io::ErrorKind::Unsupported))
                    }
                }
            }
        }

        pub fn take_error(&self) -> io::Result<()> {
            unsafe {
                let fd = self.0;
                let res = sock_get_error(fd as u32);
                if res == 0 {
                    Ok(())
                } else {
                    Err(io::Error::from_raw_os_error(res as i32))
                }
            }
        }
        pub fn recv_from(&self, _: &mut [u8]) -> io::Result<(usize, SocketAddr)> {
            Err(io::Error::from(io::ErrorKind::Unsupported))
        }
        pub fn send_to(&self, _: &[u8], _: SocketAddr) -> io::Result<usize> {
            Err(io::Error::from(io::ErrorKind::Unsupported))
        }

        pub fn shutdown(&self, how: Shutdown) -> io::Result<()> {
            use super::socket_types::*;
            unsafe {
                let flags = match how {
                    Shutdown::Read => 1,//__WASI_SDFLAGS_RD
                    Shutdown::Write => 2,//__WASI_SDFLAGS_WR
                    Shutdown::Both => 3,//__WASI_SDFLAGS_RD | __WASI_SDFLAGS_WR
                };
                sock_shutdown(self.as_raw_fd() as u32, flags as u8);
            }
            Ok(())
        }
    }

    impl<'a> Read for &'a Socket {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            self.recv(buf)
        }
    }

    impl<'a> Write for &'a Socket {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.send(buf)
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[link(wasm_import_module = "wasi_snapshot_preview1")]
    extern "C" {
        pub fn sock_open(addr_family: u8, sock_type: u8, fd: *mut u32) -> u32;
        pub fn sock_bind(fd: u32, addr: *mut WasiAddress, port: u32) -> u32;
        pub fn sock_listen(fd: u32, backlog: u32) -> u32;
        pub fn sock_accept(fd: u32, new_fd: *mut u32) -> u32;
        pub fn sock_connect(fd: u32, addr: *mut WasiAddress, port: u32) -> u32;
        pub fn sock_recv(
            fd: u32,
            buf: *const IovecRead,
            buf_len: usize,
            flags: u16,
            recv_len: *mut usize,
            oflags: *mut usize,
        ) -> u32;
        // pub fn sock_recv_from(fd: u32, buf: *mut u8, buf_len: u32, addr: *mut u8, addr_len: *mut u32, flags: u16, ) -> u32;
        pub fn sock_send(
            fd: u32,
            buf: *const IovecWrite,
            buf_len: u32,
            flags: u16,
            send_len: *mut u32,
        ) -> u32;
        // pub fn sock_send_to(fd: u32, buf: *const u8, buf_len: u32, addr: *const u8, addr_len: u32, flags: u16, ) -> u32;
        pub fn sock_shutdown(fd: u32, flags: u8) -> u32;
        pub fn sock_get_error(fd: u32) -> u32;
        pub fn sock_get_local(
            fd: u32,
            addr: *mut WasiAddress,
            addr_type: *mut u32,
            port: *mut u32,
        ) -> u32;
        pub fn sock_get_peer(
            fd: u32,
            addr: *mut WasiAddress,
            addr_type: *mut u32,
            port: *mut u32,
        ) -> u32;
    }
}

mod socket_types {
    pub const INADDR_LOOPBACK: u32 = 2130706433;
    pub const INADDR_ANY: u32 = 0;
    pub const INADDR_BROADCAST: u32 = 4294967295;
    pub const INADDR_NONE: u32 = 4294967295;

    pub const AF_INET: i32 = 2;

    pub const IPPROTO_TCP: i32 = 6;
    // pub const IPPROTO_UDP: i32 = 17;

    pub const MSG_OOB: i32 = 1;
    pub const MSG_PEEK: i32 = 2;
    pub const MSG_WAITALL: i32 = 0x100;

    pub const SHUT_RD: i32 = 0;
    pub const SHUT_WR: i32 = 1;
    pub const SHUT_RDWR: i32 = 2;

    pub const SOCK_STREAM: i32 = 1;
    // pub const SOCK_DGRAM: i32 = 2;
}

#[pymodule]
mod _socket {
    use super::wasmedge_sock as s;
    use crate::common::lock::{PyMappedRwLockReadGuard, PyRwLock, PyRwLockReadGuard};
    use crate::vm::{
        builtins::{PyBaseExceptionRef, PyListRef, PyStrRef, PyTupleRef, PyTypeRef},
        function::{
            ArgBytesLike, ArgMemoryBuffer, FuncArgs, IntoPyException, IntoPyObject, OptionalArg,
            OptionalOption,
        },
        utils::{Either, ToCString},
        PyObjectRef, PyResult, PyValue, TryFromBorrowedObject, TryFromObject, TypeProtocol,
        VirtualMachine,
    };
    use crossbeam_utils::atomic::AtomicCell;
    use num_traits::ToPrimitive;
    use std::mem::MaybeUninit;
    use std::net::{Ipv4Addr, Ipv6Addr, Shutdown, SocketAddr, SocketAddrV4, ToSocketAddrs};
    use std::ops::Deref;
    use std::time::{Duration, Instant};
    use std::{
        ffi,
        io::{self, Read, Write},
    };

    use libc as c;

    #[pyattr(name = "has_ipv6")]
    const HAS_IPV6: bool = false;

    #[pyattr]
    use super::socket_types::{
        AF_INET, IPPROTO_TCP, IPPROTO_TCP as SOL_TCP, MSG_OOB, MSG_PEEK, MSG_WAITALL, SHUT_RD,
        SHUT_RDWR, SHUT_WR, SOCK_STREAM,
    };

    #[pyattr]
    fn error(vm: &VirtualMachine) -> PyTypeRef {
        vm.ctx.exceptions.os_error.clone()
    }

    #[pyattr(once)]
    fn timeout(vm: &VirtualMachine) -> PyTypeRef {
        vm.ctx.new_exception_type(
            "socket",
            "timeout",
            Some(vec![vm.ctx.exceptions.os_error.clone()]),
        )
    }

    #[pyattr(once)]
    fn herror(vm: &VirtualMachine) -> PyTypeRef {
        vm.ctx.new_exception_type(
            "socket",
            "herror",
            Some(vec![vm.ctx.exceptions.os_error.clone()]),
        )
    }

    #[pyattr(once)]
    fn gaierror(vm: &VirtualMachine) -> PyTypeRef {
        vm.ctx.new_exception_type(
            "socket",
            "gaierror",
            Some(vec![vm.ctx.exceptions.os_error.clone()]),
        )
    }

    #[pyfunction]
    fn htonl(x: u32) -> u32 {
        u32::to_be(x)
    }

    #[pyfunction]
    fn htons(x: u16) -> u16 {
        u16::to_be(x)
    }

    #[pyfunction]
    fn ntohl(x: u32) -> u32 {
        u32::from_be(x)
    }

    #[pyfunction]
    fn ntohs(x: u16) -> u16 {
        u16::from_be(x)
    }

    type RawSocket = s::RawSocket;
    type Socket = s::Socket;

    fn get_raw_sock(obj: PyObjectRef, vm: &VirtualMachine) -> PyResult<RawSocket> {
        type CastFrom = libc::c_long;

        // should really just be to_index() but test_socket tests the error messages explicitly
        if obj.isinstance(&vm.ctx.types.float_type) {
            return Err(vm.new_type_error("integer argument expected, got float".to_owned()));
        }
        let int = vm
            .to_index_opt(obj)
            .unwrap_or_else(|| Err(vm.new_type_error("an integer is required".to_owned())))?;
        int.try_to_primitive::<CastFrom>(vm)
            .map(|sock| sock as RawSocket)
    }

    mod nullable_socket {
        use super::*;
        use std::os::wasi::prelude::AsRawFd;

        #[derive(Debug)]
        #[repr(transparent)]
        pub struct NullableSocket(Option<Socket>);

        impl From<Socket> for NullableSocket {
            fn from(sock: Socket) -> Self {
                NullableSocket(Some(sock))
            }
        }

        impl NullableSocket {
            pub fn invalid() -> Self {
                Self(None)
            }
            pub fn get(&self) -> Option<&Socket> {
                self.0.as_ref()
            }
            pub fn fd(&self) -> RawSocket {
                self.get().map_or(INVALID_SOCKET, |sock| sock.as_raw_fd())
            }
            pub fn insert(&mut self, sock: Socket) -> &mut Socket {
                self.0.insert(sock)
            }
        }
    }

    use nullable_socket::NullableSocket;

    impl Default for NullableSocket {
        fn default() -> Self {
            Self::invalid()
        }
    }

    #[pyattr(name = "socket")]
    #[pyattr(name = "SocketType")]
    #[pyclass(module = "socket", name = "socket")]
    #[derive(Debug, PyValue)]
    pub struct PySocket {
        kind: AtomicCell<i32>,
        family: AtomicCell<i32>,
        proto: AtomicCell<i32>,
        pub(crate) timeout: AtomicCell<f64>,
        sock: PyRwLock<NullableSocket>,
    }

    impl Default for PySocket {
        fn default() -> Self {
            PySocket {
                kind: AtomicCell::default(),
                family: AtomicCell::default(),
                proto: AtomicCell::default(),
                timeout: AtomicCell::new(-1.0),
                sock: PyRwLock::new(NullableSocket::invalid()),
            }
        }
    }

    const CLOSED_ERR: i32 = c::EBADF;

    impl Read for &PySocket {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            let s = (&mut &*self.sock_io()?);
            s.read(buf)
        }
    }

    impl Write for &PySocket {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            let s = (&mut &*self.sock_io()?);
            s.write(buf)
        }

        fn flush(&mut self) -> std::io::Result<()> {
            (&mut &*self.sock_io()?).flush()
        }
    }

    impl PySocket {
        pub fn sock_opt(&self) -> Option<PyMappedRwLockReadGuard<'_, Socket>> {
            PyRwLockReadGuard::try_map(self.sock.read(), |sock| sock.get()).ok()
        }

        fn sock_io(&self) -> io::Result<PyMappedRwLockReadGuard<'_, Socket>> {
            self.sock_opt()
                .ok_or_else(|| io::Error::from_raw_os_error(CLOSED_ERR))
        }

        pub fn sock(&self, vm: &VirtualMachine) -> PyResult<PyMappedRwLockReadGuard<'_, Socket>> {
            self.sock_io().map_err(|e| e.into_pyexception(vm))
        }

        fn init_inner(
            &self,
            family: i32,
            socket_kind: i32,
            proto: i32,
            sock: Socket,
            vm: &VirtualMachine,
        ) -> PyResult<()> {
            self.family.store(family);
            self.kind.store(socket_kind);
            self.proto.store(proto);
            let mut s = self.sock.write();
            let sock = s.insert(sock);
            let timeout = DEFAULT_TIMEOUT.load();
            self.timeout.store(timeout);
            if timeout >= 0.0 {
                sock.set_nonblocking(true)
                    .map_err(|e| e.into_pyexception(vm))?;
            }
            Ok(())
        }

        #[inline]
        fn sock_op<F, R>(&self, vm: &VirtualMachine, select: SelectKind, f: F) -> PyResult<R>
        where
            F: FnMut() -> io::Result<R>,
        {
            self.sock_op_err(vm, select, f)
                .map_err(|e| e.into_pyexception(vm))
        }

        /// returns Err(blocking)
        pub fn get_timeout(&self) -> Result<Duration, bool> {
            let timeout = self.timeout.load();
            if timeout > 0.0 {
                Ok(Duration::from_secs_f64(timeout))
            } else {
                Err(timeout != 0.0)
            }
        }

        fn sock_op_err<F, R>(
            &self,
            vm: &VirtualMachine,
            select: SelectKind,
            f: F,
        ) -> Result<R, IoOrPyException>
        where
            F: FnMut() -> io::Result<R>,
        {
            self.sock_op_timeout_err(vm, select, self.get_timeout().ok(), f)
        }

        fn sock_op_timeout_err<F, R>(
            &self,
            vm: &VirtualMachine,
            select: SelectKind,
            timeout: Option<Duration>,
            mut f: F,
        ) -> Result<R, IoOrPyException>
        where
            F: FnMut() -> io::Result<R>,
        {
            let deadline = timeout.map(Deadline::new);

            loop {
                if deadline.is_some() || matches!(select, SelectKind::Connect) {
                    let interval = deadline.as_ref().map(|d| d.time_until()).transpose()?;
                    let res = sock_select(&*self.sock(vm)?, select, interval);
                    match res {
                        Ok(true) => return Err(IoOrPyException::Timeout),
                        Err(e) if e.kind() == io::ErrorKind::Interrupted => {
                            vm.check_signals()?;
                            continue;
                        }
                        Err(e) => return Err(e.into()),
                        Ok(false) => {} // no timeout, continue as normal
                    }
                }

                let err = loop {
                    // loop on interrupt
                    match f() {
                        Ok(x) => return Ok(x),
                        Err(e) if e.kind() == io::ErrorKind::Interrupted => vm.check_signals()?,
                        Err(e) => break e,
                    }
                };
                if timeout.is_some() && err.kind() == io::ErrorKind::WouldBlock {
                    continue;
                }
                return Err(err.into());
            }
        }

        fn extract_address(
            &self,
            addr: PyObjectRef,
            caller: &str,
            vm: &VirtualMachine,
        ) -> PyResult<SocketAddr> {
            let family = self.family.load();
            match family {
                AF_INET => {
                    let tuple: PyTupleRef = addr.downcast().map_err(|obj| {
                        vm.new_type_error(format!(
                            "{}(): AF_INET address must be tuple, not {}",
                            caller,
                            obj.class().name()
                        ))
                    })?;
                    let tuple = tuple.as_slice();
                    if tuple.len() != 2 {
                        return Err(vm.new_type_error(
                            "AF_INET address must be a pair (host, post)".to_owned(),
                        ));
                    }
                    let addr = Address::from_tuple(tuple, vm)?;
                    let mut addr4 = get_addr(vm, addr.host, AF_INET)?;
                    match &mut addr4 {
                        SocketAddr::V4(addr4) => {
                            addr4.set_port(addr.port);
                        }
                        SocketAddr::V6(_) => unreachable!(),
                    }
                    Ok(addr4)
                }
                _ => Err(vm.new_os_error(format!("{}(): bad family", caller))),
            }
        }

        fn connect_inner(
            &self,
            address: PyObjectRef,
            caller: &str,
            vm: &VirtualMachine,
        ) -> Result<(), IoOrPyException> {
            let sock_addr = self.extract_address(address, caller, vm)?;

            let err = match self.sock(vm)?.connect(&sock_addr) {
                Ok(()) => return Ok(()),
                Err(e) => e,
            };

            let wait_connect = if err.kind() == io::ErrorKind::Interrupted {
                vm.check_signals()?;
                self.timeout.load() != 0.0
            } else {
                use c::EINPROGRESS;
                self.timeout.load() > 0.0 && err.raw_os_error() == Some(EINPROGRESS)
            };

            if wait_connect {
                // basically, connect() is async, and it registers an "error" on the socket when it's
                // done connecting. SelectKind::Connect fills the errorfds fd_set, so if we wake up
                // from poll and the error is EISCONN then we know that the connect is done
                self.sock_op_err(vm, SelectKind::Connect, || {
                    let sock = self.sock_io()?;
                    let err = sock.take_error();
                    match err {
                        Err(e) if e.raw_os_error() == Some(libc::EISCONN) => Ok(()),
                        Err(e) => Err(e),
                        // TODO: is this accurate?
                        Ok(()) => Ok(()),
                    }
                })
            } else {
                Err(err.into())
            }
        }
    }

    #[pyimpl(flags(BASETYPE))]
    impl PySocket {
        #[pyslot]
        fn slot_new(cls: PyTypeRef, _args: FuncArgs, vm: &VirtualMachine) -> PyResult {
            Self::default().into_pyresult_with_type(vm, cls)
        }

        #[pymethod(magic)]
        fn init(
            &self,
            family: OptionalArg<i32>,
            socket_kind: OptionalArg<i32>,
            proto: OptionalArg<i32>,
            fileno: OptionalOption<PyObjectRef>,
            vm: &VirtualMachine,
        ) -> PyResult<()> {
            let mut family = family.unwrap_or(-1);
            let mut socket_kind = socket_kind.unwrap_or(-1);
            let mut proto = proto.unwrap_or(-1);
            let fileno = fileno
                .flatten()
                .map(|obj| get_raw_sock(obj, vm))
                .transpose()?;
            let sock;
            if let Some(fileno) = fileno {
                sock = sock_from_raw(fileno, vm)?;
            } else {
                if family == -1 {
                    family = AF_INET as i32
                }
                if socket_kind == -1 {
                    socket_kind = SOCK_STREAM
                }
                if proto == -1 {
                    proto = 0
                }
                sock = Socket::new(family, socket_kind).map_err(|e| e.into_pyexception(vm))?;
            };
            self.init_inner(family, socket_kind, proto, sock, vm)
        }

        #[pymethod]
        fn connect(&self, address: PyObjectRef, vm: &VirtualMachine) -> PyResult<()> {
            self.connect_inner(address, "connect", vm)
                .map_err(|e| e.into_pyexception(vm))
        }

        #[pymethod]
        fn connect_ex(&self, address: PyObjectRef, vm: &VirtualMachine) -> PyResult<i32> {
            match self.connect_inner(address, "connect_ex", vm) {
                Ok(()) => Ok(0),
                Err(err) => err.errno(),
            }
        }

        #[pymethod]
        fn bind(&self, address: PyObjectRef, vm: &VirtualMachine) -> PyResult<()> {
            let sock_addr = self.extract_address(address, "bind", vm)?;
            self.sock(vm)?
                .bind(&sock_addr)
                .map_err(|err| err.into_pyexception(vm))?;
            Ok(())
        }

        #[pymethod]
        fn listen(&self, backlog: OptionalArg<i32>, vm: &VirtualMachine) -> PyResult<()> {
            let backlog = backlog.unwrap_or(128);
            let backlog = if backlog < 0 { 0 } else { backlog };
            self.sock(vm)?
                .listen(backlog)
                .map_err(|err| err.into_pyexception(vm))
        }

        #[pymethod]
        fn _accept(&self, vm: &VirtualMachine) -> PyResult<(RawSocket, PyObjectRef)> {
            let sock = self.sock_op(vm, SelectKind::Read, || self.sock_io()?.accept())?;
            let addr = sock.get_peer().map_err(|e| e.into_pyexception(vm))?;
            let fd = into_sock_fileno(sock);
            Ok((fd, get_addr_tuple(&addr, vm)))
        }

        #[pymethod]
        fn recv(
            &self,
            bufsize: usize,
            flags: OptionalArg<i32>,
            vm: &VirtualMachine,
        ) -> PyResult<Vec<u8>> {
            let _flags = flags.unwrap_or(0);
            let mut buffer = vec![0u8; bufsize];
            let sock = self.sock(vm)?;
            let n = self.sock_op(vm, SelectKind::Read, || sock.recv(&mut buffer))?;
            unsafe { buffer.set_len(n) };
            Ok(buffer)
        }

        #[pymethod]
        fn recv_into(
            &self,
            buf: ArgMemoryBuffer,
            flags: OptionalArg<i32>,
            vm: &VirtualMachine,
        ) -> PyResult<usize> {
            let _flags = flags.unwrap_or(0);
            let sock = self.sock(vm)?;
            let mut buf = buf.borrow_buf_mut();
            let buf = &mut *buf;
            self.sock_op(vm, SelectKind::Read, || sock.recv(buf))
        }

        #[pymethod]
        fn recvfrom(
            &self,
            bufsize: isize,
            flags: OptionalArg<i32>,
            vm: &VirtualMachine,
        ) -> PyResult<(Vec<u8>, PyObjectRef)> {
            let _flags = flags.unwrap_or(0);
            let bufsize = bufsize
                .to_usize()
                .ok_or_else(|| vm.new_value_error("negative buffersize in recvfrom".to_owned()))?;
            let mut buffer = vec![0u8; bufsize];
            let (n, addr) = self.sock_op(vm, SelectKind::Read, || {
                self.sock_io()?.recv_from(&mut buffer)
            })?;
            unsafe { buffer.set_len(n) };
            Ok((buffer, get_addr_tuple(&addr, vm)))
        }

        #[pymethod]
        fn recvfrom_into(
            &self,
            buf: ArgMemoryBuffer,
            nbytes: OptionalArg<isize>,
            flags: OptionalArg<i32>,
            vm: &VirtualMachine,
        ) -> PyResult<(usize, PyObjectRef)> {
            let mut buf = buf.borrow_buf_mut();
            let buf = &mut *buf;
            let buf = match nbytes {
                OptionalArg::Present(i) => {
                    let i = i.to_usize().ok_or_else(|| {
                        vm.new_value_error("negative buffersize in recvfrom_into".to_owned())
                    })?;
                    buf.get_mut(..i).ok_or_else(|| {
                        vm.new_value_error(
                            "nbytes is greater than the length of the buffer".to_owned(),
                        )
                    })?
                }
                OptionalArg::Missing => buf,
            };
            let flags = flags.unwrap_or(0);
            let sock = self.sock(vm)?;
            let (n, addr) = self.sock_op(vm, SelectKind::Read, || sock.recv_from(buf))?;
            Ok((n, get_addr_tuple(&addr, vm)))
        }

        #[pymethod]
        fn send(
            &self,
            bytes: ArgBytesLike,
            flags: OptionalArg<i32>,
            vm: &VirtualMachine,
        ) -> PyResult<usize> {
            let _flags = flags.unwrap_or(0);
            let buf = bytes.borrow_buf();
            let buf = &*buf;
            self.sock_op(vm, SelectKind::Write, || self.sock_io()?.send(buf))
        }

        #[pymethod]
        fn sendall(
            &self,
            bytes: ArgBytesLike,
            flags: OptionalArg<i32>,
            vm: &VirtualMachine,
        ) -> PyResult<()> {
            let flags = flags.unwrap_or(0);

            let timeout = self.get_timeout().ok();

            let deadline = timeout.map(Deadline::new);

            let buf = bytes.borrow_buf();
            let buf = &*buf;
            let mut buf_offset = 0;
            // now we have like 3 layers of interrupt loop :)
            while buf_offset < buf.len() {
                let interval = deadline
                    .as_ref()
                    .map(|d| d.time_until().map_err(|e| e.into_pyexception(vm)))
                    .transpose()?;
                self.sock_op_timeout_err(vm, SelectKind::Write, interval, || {
                    let subbuf = &buf[buf_offset..];
                    buf_offset += self.sock_io()?.send(subbuf)?;
                    Ok(())
                })
                .map_err(|e| e.into_pyexception(vm))?;
                vm.check_signals()?;
            }
            Ok(())
        }

        #[pymethod]
        fn sendto(
            &self,
            bytes: ArgBytesLike,
            arg2: PyObjectRef,
            arg3: OptionalArg<PyObjectRef>,
            vm: &VirtualMachine,
        ) -> PyResult<usize> {
            // signature is bytes[, flags], address
            let (flags, address) = match arg3 {
                OptionalArg::Present(arg3) => {
                    // should just be i32::try_from_obj but tests check for error message
                    let int = vm.to_index_opt(arg2).unwrap_or_else(|| {
                        Err(vm.new_type_error("an integer is required".to_owned()))
                    })?;
                    let flags = int.try_to_primitive::<i32>(vm)?;
                    (flags, arg3)
                }
                OptionalArg::Missing => (0, arg2),
            };
            let addr = self.extract_address(address, "sendto", vm)?;
            let buf = bytes.borrow_buf();
            let buf = &*buf;
            self.sock_op(vm, SelectKind::Write, move || {
                self.sock_io()?.send_to(buf, addr)
            })
        }

        #[pymethod]
        fn close(&self, vm: &VirtualMachine) -> PyResult<()> {
            let sock = self.detach();
            if sock != INVALID_SOCKET {
                close_inner(sock, vm)?;
            }
            Ok(())
        }
        #[pymethod]
        #[inline]
        fn detach(&self) -> RawSocket {
            let sock = std::mem::replace(&mut *self.sock.write(), NullableSocket::invalid());
            std::mem::ManuallyDrop::new(sock).fd()
        }

        #[pymethod]
        fn fileno(&self) -> RawSocket {
            self.sock.read().fd()
        }

        #[pymethod]
        fn getsockname(&self, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
            let addr = self
                .sock(vm)?
                .get_local()
                .map_err(|err| err.into_pyexception(vm))?;

            Ok(get_addr_tuple(&addr, vm))
        }
        #[pymethod]
        fn getpeername(&self, vm: &VirtualMachine) -> PyResult<PyObjectRef> {
            let addr = self
                .sock(vm)?
                .get_peer()
                .map_err(|err| err.into_pyexception(vm))?;

            Ok(get_addr_tuple(&addr, vm))
        }

        #[pymethod]
        fn gettimeout(&self) -> Option<f64> {
            let timeout = self.timeout.load();
            if timeout >= 0.0 {
                Some(timeout)
            } else {
                None
            }
        }

        #[pymethod]
        fn setblocking(&self, block: bool, vm: &VirtualMachine) -> PyResult<()> {
            self.timeout.store(if block { -1.0 } else { 0.0 });
            self.sock(vm)?
                .set_nonblocking(!block)
                .map_err(|err| err.into_pyexception(vm))
        }

        #[pymethod]
        fn getblocking(&self) -> bool {
            self.timeout.load() != 0.0
        }

        #[pymethod]
        fn settimeout(&self, timeout: Option<Duration>, vm: &VirtualMachine) -> PyResult<()> {
            self.timeout
                .store(timeout.map_or(-1.0, |d| d.as_secs_f64()));
            // even if timeout is > 0 the socket needs to be nonblocking in order for us to select() on
            // it
            self.sock(vm)?
                .set_nonblocking(timeout.is_some())
                .map_err(|err| err.into_pyexception(vm))
        }

        #[pymethod]
        fn getsockopt(
            &self,
            level: i32,
            name: i32,
            buflen: OptionalArg<i32>,
            vm: &VirtualMachine,
        ) -> PyResult {
            return Err(vm.new_os_error("getsockopt no support".to_owned()));
        }

        #[pymethod]
        fn setsockopt(
            &self,
            level: i32,
            name: i32,
            value: Option<Either<ArgBytesLike, i32>>,
            optlen: OptionalArg<u32>,
            vm: &VirtualMachine,
        ) -> PyResult<()> {
            Ok(())
        }

        #[pymethod]
        fn shutdown(&self, how: i32, vm: &VirtualMachine) -> PyResult<()> {
            let how = match how {
                SHUT_RD => Shutdown::Read,
                SHUT_WR => Shutdown::Write,
                SHUT_RDWR => Shutdown::Both,
                _ => {
                    return Err(vm.new_value_error(
                        "`how` must be SHUT_RD, SHUT_WR, or SHUT_RDWR".to_owned(),
                    ));
                }
            };
            self.sock(vm)?
                .shutdown(how)
                .map_err(|err| err.into_pyexception(vm))
        }

        #[pyproperty(name = "type")]
        fn kind(&self) -> i32 {
            self.kind.load()
        }
        #[pyproperty]
        fn family(&self) -> i32 {
            self.family.load()
        }
        #[pyproperty]
        fn proto(&self) -> i32 {
            self.proto.load()
        }

        #[pymethod(magic)]
        fn repr(&self) -> String {
            format!(
                "<socket object, fd={}, family={}, type={}, proto={}>",
                // cast because INVALID_SOCKET is unsigned, so would show usize::MAX instead of -1
                self.sock.read().fd() as i64,
                self.family.load(),
                self.kind.load(),
                self.proto.load(),
            )
        }
    }

    struct Address {
        host: PyStrRef,
        port: u16,
    }

    impl ToSocketAddrs for Address {
        type Iter = std::vec::IntoIter<SocketAddr>;
        fn to_socket_addrs(&self) -> io::Result<Self::Iter> {
            (self.host.as_str(), self.port).to_socket_addrs()
        }
    }

    impl TryFromObject for Address {
        fn try_from_object(vm: &VirtualMachine, obj: PyObjectRef) -> PyResult<Self> {
            let tuple = PyTupleRef::try_from_object(vm, obj)?;
            if tuple.as_slice().len() != 2 {
                Err(vm.new_type_error("Address tuple should have only 2 values".to_owned()))
            } else {
                Self::from_tuple(tuple.as_slice(), vm)
            }
        }
    }

    impl Address {
        fn from_tuple(tuple: &[PyObjectRef], vm: &VirtualMachine) -> PyResult<Self> {
            let host = PyStrRef::try_from_object(vm, tuple[0].clone())?;
            let port = i32::try_from_borrowed_object(vm, &tuple[1])?;
            let port = port
                .to_u16()
                .ok_or_else(|| vm.new_overflow_error("port must be 0-65535.".to_owned()))?;
            Ok(Address { host, port })
        }
        fn from_tuple_ipv6(
            tuple: &[PyObjectRef],
            vm: &VirtualMachine,
        ) -> PyResult<(Self, u32, u32)> {
            let addr = Address::from_tuple(tuple, vm)?;
            let flowinfo = tuple
                .get(2)
                .map(|obj| u32::try_from_borrowed_object(vm, obj))
                .transpose()?
                .unwrap_or(0);
            let scopeid = tuple
                .get(3)
                .map(|obj| u32::try_from_borrowed_object(vm, obj))
                .transpose()?
                .unwrap_or(0);
            if flowinfo > 0xfffff {
                return Err(vm.new_overflow_error("flowinfo must be 0-1048575.".to_owned()));
            }
            Ok((addr, flowinfo, scopeid))
        }
    }

    fn get_ip_addr_tuple(addr: &SocketAddr, vm: &VirtualMachine) -> PyObjectRef {
        match addr {
            SocketAddr::V4(addr) => (addr.ip().to_string(), addr.port()).into_pyobject(vm),
            SocketAddr::V6(addr) => (
                addr.ip().to_string(),
                addr.port(),
                addr.flowinfo(),
                addr.scope_id(),
            )
                .into_pyobject(vm),
        }
    }

    fn get_addr_tuple(addr: &SocketAddr, vm: &VirtualMachine) -> PyObjectRef {
        (addr.ip().to_string(), addr.port()).into_pyobject(vm)
    }

    #[pyfunction]
    fn gethostname(vm: &VirtualMachine) -> PyResult<PyStrRef> {
        Ok(vm.ctx.new_str("unknowns").into())
    }

    #[pyfunction]
    fn inet_aton(ip_string: PyStrRef, vm: &VirtualMachine) -> PyResult<Vec<u8>> {
        ip_string
            .as_str()
            .parse::<Ipv4Addr>()
            .map(|ip_addr| Vec::<u8>::from(ip_addr.octets()))
            .map_err(|_| {
                vm.new_os_error("illegal IP address string passed to inet_aton".to_owned())
            })
    }

    #[pyfunction]
    fn inet_ntoa(packed_ip: ArgBytesLike, vm: &VirtualMachine) -> PyResult<PyStrRef> {
        let packed_ip = packed_ip.borrow_buf();
        let packed_ip = <&[u8; 4]>::try_from(&*packed_ip)
            .map_err(|_| vm.new_os_error("packed IP wrong length for inet_ntoa".to_owned()))?;
        Ok(vm.ctx.new_str(Ipv4Addr::from(*packed_ip).to_string()))
    }

    fn cstr_opt_as_ptr(x: &OptionalArg<ffi::CString>) -> *const libc::c_char {
        x.as_ref().map_or_else(std::ptr::null, |s| s.as_ptr())
    }

    #[pyfunction]
    fn getservbyname(
        _servicename: PyStrRef,
        _protocolname: OptionalArg<PyStrRef>,
        vm: &VirtualMachine,
    ) -> PyResult<u16> {
        Err(vm.new_os_error("service/proto not found".to_owned()))
    }

    #[pyfunction]
    fn getservbyport(
        port: i32,
        _protocolname: OptionalArg<PyStrRef>,
        vm: &VirtualMachine,
    ) -> PyResult<String> {
        let _ = port.to_u16().ok_or_else(|| {
            vm.new_overflow_error("getservbyport: port must be 0-65535.".to_owned())
        })?;
        return Err(vm.new_os_error("port/proto not found".to_owned()));
    }

    // TODO: use `Vec::spare_capacity_mut` once stable.
    fn spare_capacity_mut<T>(v: &mut Vec<T>) -> &mut [MaybeUninit<T>] {
        let (len, cap) = (v.len(), v.capacity());
        unsafe {
            std::slice::from_raw_parts_mut(
                v.as_mut_ptr().add(len) as *mut MaybeUninit<T>,
                cap - len,
            )
        }
    }

    fn slice_as_uninit<T>(v: &mut [T]) -> &mut [MaybeUninit<T>] {
        unsafe { &mut *(v as *mut [T] as *mut [MaybeUninit<T>]) }
    }

    enum IoOrPyException {
        Timeout,
        Py(PyBaseExceptionRef),
        Io(io::Error),
    }

    impl From<PyBaseExceptionRef> for IoOrPyException {
        fn from(exc: PyBaseExceptionRef) -> Self {
            Self::Py(exc)
        }
    }

    impl From<io::Error> for IoOrPyException {
        fn from(err: io::Error) -> Self {
            Self::Io(err)
        }
    }

    use c::EINPROGRESS;

    impl IoOrPyException {
        fn errno(self) -> PyResult<i32> {
            match self {
                Self::Timeout => Ok(EINPROGRESS),
                Self::Io(err) => {
                    // TODO: just unwrap()?
                    Ok(err.raw_os_error().unwrap_or(1))
                }
                Self::Py(exc) => Err(exc),
            }
        }
    }

    impl IntoPyException for IoOrPyException {
        fn into_pyexception(self, vm: &VirtualMachine) -> PyBaseExceptionRef {
            match self {
                Self::Timeout => timeout_error(vm),
                Self::Py(exc) => exc,
                Self::Io(err) => err.into_pyexception(vm),
            }
        }
    }

    #[derive(Copy, Clone)]
    pub(crate) enum SelectKind {
        Read,
        Write,
        Connect,
    }

    /// returns true if timed out
    pub(crate) fn sock_select(
        sock: &Socket,
        kind: SelectKind,
        interval: Option<Duration>,
    ) -> io::Result<bool> {
        let fd = sock_fileno(sock);

        let mut pollfd = libc::pollfd {
            fd,
            events: match kind {
                SelectKind::Read => libc::POLLIN,
                SelectKind::Write => libc::POLLOUT,
                SelectKind::Connect => libc::POLLOUT | libc::POLLERR,
            },
            revents: 0,
        };
        let timeout = match interval {
            Some(d) => d.as_millis() as _,
            None => -1,
        };
        let ret = unsafe { libc::poll(&mut pollfd, 1, timeout) };
        if ret < 0 {
            Err(io::Error::last_os_error())
        } else {
            Ok(ret == 0)
        }
    }

    #[derive(FromArgs)]
    struct GAIOptions {
        #[pyarg(positional)]
        host: Option<PyStrRef>,
        #[pyarg(positional)]
        port: Option<Either<PyStrRef, i32>>,

        #[pyarg(positional, default = "AF_INET")]
        family: i32,
        #[pyarg(positional, default = "0")]
        ty: i32,
        #[pyarg(positional, default = "0")]
        proto: i32,
        #[pyarg(positional, default = "0")]
        flags: i32,
    }

    #[pyfunction]
    fn getaddrinfo(opts: GAIOptions, vm: &VirtualMachine) -> PyResult<Vec<PyObjectRef>> {
        Err(vm.new_os_error("DNS not supported".to_owned()))
    }

    #[pyfunction]
    fn gethostbyaddr(
        addr: PyStrRef,
        vm: &VirtualMachine,
    ) -> PyResult<(String, PyListRef, PyListRef)> {
        Err(vm.new_os_error("DNS not supported".to_owned()))
    }

    #[pyfunction]
    fn gethostbyname(name: PyStrRef, vm: &VirtualMachine) -> PyResult<String> {
        Err(vm.new_os_error("DNS not supported".to_owned()))
    }

    #[pyfunction]
    fn gethostbyname_ex(
        name: PyStrRef,
        vm: &VirtualMachine,
    ) -> PyResult<(String, PyListRef, PyListRef)> {
        Err(vm.new_os_error("DNS not supported".to_owned()))
    }

    #[pyfunction]
    fn inet_pton(af_inet: i32, ip_string: PyStrRef, vm: &VirtualMachine) -> PyResult<Vec<u8>> {
        static ERROR_MSG: &str = "illegal IP address string passed to inet_pton";
        let ip_addr = match af_inet {
            AF_INET => ip_string
                .as_str()
                .parse::<Ipv4Addr>()
                .map_err(|_| vm.new_os_error(ERROR_MSG.to_owned()))?
                .octets()
                .to_vec(),
            _ => return Err(vm.new_os_error("Address family not supported by protocol".to_owned())),
        };
        Ok(ip_addr)
    }

    #[pyfunction]
    fn inet_ntop(af_inet: i32, packed_ip: ArgBytesLike, vm: &VirtualMachine) -> PyResult<String> {
        let packed_ip = packed_ip.borrow_buf();
        match af_inet {
            AF_INET => {
                let packed_ip = <&[u8; 4]>::try_from(&*packed_ip).map_err(|_| {
                    vm.new_value_error("invalid length of packed IP address string".to_owned())
                })?;
                Ok(Ipv4Addr::from(*packed_ip).to_string())
            }
            _ => Err(vm.new_value_error(format!("unknown address family {}", af_inet))),
        }
    }

    #[pyfunction]
    fn getprotobyname(name: PyStrRef, vm: &VirtualMachine) -> PyResult {
        Err(vm.new_os_error("protocol not found".to_owned()))
    }

    #[pyfunction]
    fn getnameinfo(
        address: PyTupleRef,
        flags: i32,
        vm: &VirtualMachine,
    ) -> PyResult<(String, String)> {
        Err(vm.new_os_error("DNS not supported".to_owned()))
    }

    fn get_addr(vm: &VirtualMachine, pyname: PyStrRef, af: i32) -> PyResult<SocketAddr> {
        let name = pyname.as_str();
        if name.is_empty() {
            return Ok(SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0)));
        }
        if name == "255.255.255.255" || name == "<broadcast>" {
            if af != AF_INET {
                return Err(vm.new_os_error("address family mismatched".to_owned()));
            }
            return Ok(SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::BROADCAST, 0)));
        }
        if let AF_INET = af {
            if let Ok(addr) = name.parse::<Ipv4Addr>() {
                return Ok(SocketAddr::V4(SocketAddrV4::new(addr, 0)));
            }
        } else {
            return Err(vm.new_os_error("only support IPv4".to_owned()));
        }

        return Err(vm.new_os_error("not support DNS".to_owned()));
    }

    fn sock_from_raw(fileno: RawSocket, vm: &VirtualMachine) -> PyResult<Socket> {
        if fileno < 0 {
            return Err(vm.new_value_error("negative file descriptor".to_owned()));
        }
        Ok(unsafe { sock_from_raw_unchecked(fileno) })
    }

    /// SAFETY: fileno must not be equal to INVALID_SOCKET
    unsafe fn sock_from_raw_unchecked(fileno: RawSocket) -> Socket {
        s::Socket(fileno)
    }

    pub(super) fn sock_fileno(sock: &Socket) -> RawSocket {
        use std::os::wasi::io::AsRawFd;
        sock.as_raw_fd()
    }

    fn into_sock_fileno(sock: Socket) -> RawSocket {
        let fd = sock.0;
        std::mem::forget(sock);
        fd
    }

    pub(super) const INVALID_SOCKET: RawSocket = -1;

    fn timeout_error(vm: &VirtualMachine) -> PyBaseExceptionRef {
        timeout_error_msg(vm, "timed out".to_owned())
    }

    pub(crate) fn timeout_error_msg(vm: &VirtualMachine, msg: String) -> PyBaseExceptionRef {
        vm.new_exception_msg(timeout(vm), msg)
    }

    fn get_ipv6_addr_str(ipv6: Ipv6Addr) -> String {
        match ipv6.to_ipv4() {
            // instead of "::0.0.ddd.ddd" it's "::xxxx"
            Some(v4) if !ipv6.is_unspecified() && matches!(v4.octets(), [0, 0, _, _]) => {
                format!("::{:x}", u32::from(v4))
            }
            _ => ipv6.to_string(),
        }
    }

    pub(crate) struct Deadline {
        deadline: Instant,
    }

    impl Deadline {
        fn new(timeout: Duration) -> Self {
            Self {
                deadline: Instant::now() + timeout,
            }
        }
        fn time_until(&self) -> Result<Duration, IoOrPyException> {
            self.deadline
                .checked_duration_since(Instant::now())
                // past the deadline already
                .ok_or(IoOrPyException::Timeout)
        }
    }

    static DEFAULT_TIMEOUT: AtomicCell<f64> = AtomicCell::new(-1.0);

    #[pyfunction]
    fn getdefaulttimeout() -> Option<f64> {
        let timeout = DEFAULT_TIMEOUT.load();
        if timeout >= 0.0 {
            Some(timeout)
        } else {
            None
        }
    }

    #[pyfunction]
    fn setdefaulttimeout(timeout: Option<Duration>) {
        DEFAULT_TIMEOUT.store(timeout.map_or(-1.0, |d| d.as_secs_f64()));
    }

    #[pyfunction]
    fn dup(x: PyObjectRef, vm: &VirtualMachine) -> PyResult<RawSocket> {
        let sock = get_raw_sock(x, vm)?;
        Ok(sock)
    }

    #[pyfunction]
    fn close(x: PyObjectRef, vm: &VirtualMachine) -> PyResult<()> {
        close_inner(get_raw_sock(x, vm)?, vm)
    }

    fn close_inner(x: RawSocket, vm: &VirtualMachine) -> PyResult<()> {
        unsafe { s::sock_shutdown(x as u32, 3) };
        Ok(())
    }

    enum SocketError {
        HError,
        GaiError,
    }
}
