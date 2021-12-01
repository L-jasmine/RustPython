use rustpython_vm::{PyObjectRef, PyResult, TryFromObject, VirtualMachine};

pub(crate) fn make_module(vm: &VirtualMachine) -> PyObjectRef {
    decl::make_module(vm)
}

#[pymodule(name = "select")]
mod decl {
    use super::*;
    use crate::vm::{
        function::{IntoPyException, OptionalOption},
        stdlib::time,
        utils::Either,
        PyObjectRef, PyResult, VirtualMachine,
    };

    #[pyfunction]
    fn select(
        rlist: PyObjectRef,
        wlist: PyObjectRef,
        xlist: PyObjectRef,
        timeout: OptionalOption<Either<f64, isize>>,
        vm: &VirtualMachine,
    ) -> PyResult<(PyListRef, PyListRef, PyListRef)> {
        let err = std::io::Error::from(std::io::ErrorKind::Unsupported);
        Err(err.into_pyexception(vm))
    }

    #[pyfunction]
    fn poll() -> poll::PyPoll {
        poll::PyPoll::default()
    }

    #[pyattr]
    use libc::{POLLERR, POLLHUP, POLLIN, POLLNVAL, POLLOUT};
    use rustpython_vm::builtins::PyListRef;

    pub(super) mod poll {
        use super::*;
        use crate::vm::{
            builtins::PyFloat,
            common::lock::PyMutex,
            function::{IntoPyObject, OptionalArg},
            stdlib::io::Fildes,
            PyValue, TypeProtocol,
        };
        use libc::pollfd;
        use num_traits::ToPrimitive;
        use std::time;

        #[pyclass(module = "select", name = "poll")]
        #[derive(Default, Debug, PyValue)]
        pub struct PyPoll {
            // keep sorted
            fds: PyMutex<Vec<pollfd>>,
        }

        #[inline]
        fn search(fds: &[pollfd], fd: i32) -> Result<usize, usize> {
            fds.binary_search_by_key(&fd, |pfd| pfd.fd)
        }

        fn insert_fd(fds: &mut Vec<pollfd>, fd: i32, events: i16) {
            match search(fds, fd) {
                Ok(i) => fds[i].events = events,
                Err(i) => fds.insert(
                    i,
                    pollfd {
                        fd,
                        events,
                        revents: 0,
                    },
                ),
            }
        }

        fn get_fd_mut(fds: &mut [pollfd], fd: i32) -> Option<&mut pollfd> {
            search(fds, fd).ok().map(move |i| &mut fds[i])
        }

        fn remove_fd(fds: &mut Vec<pollfd>, fd: i32) -> Option<pollfd> {
            search(fds, fd).ok().map(|i| fds.remove(i))
        }

        const DEFAULT_EVENTS: i16 = libc::POLLIN | libc::POLLOUT;

        #[pyimpl]
        impl PyPoll {
            #[pymethod]
            fn register(&self, Fildes(fd): Fildes, eventmask: OptionalArg<u16>) {
                insert_fd(
                    &mut self.fds.lock(),
                    fd,
                    eventmask.map_or(DEFAULT_EVENTS, |e| e as i16),
                )
            }

            #[pymethod]
            fn modify(
                &self,
                Fildes(fd): Fildes,
                eventmask: u16,
                vm: &VirtualMachine,
            ) -> PyResult<()> {
                let mut fds = self.fds.lock();
                let pfd = get_fd_mut(&mut fds, fd).ok_or_else(|| {
                    std::io::Error::from_raw_os_error(libc::ENOENT).into_pyexception(vm)
                })?;
                pfd.events = eventmask as i16;
                Ok(())
            }

            #[pymethod]
            fn unregister(&self, Fildes(fd): Fildes, vm: &VirtualMachine) -> PyResult<()> {
                let removed = remove_fd(&mut self.fds.lock(), fd);
                removed
                    .map(drop)
                    .ok_or_else(|| vm.new_key_error(vm.ctx.new_int(fd).into()))
            }

            #[pymethod]
            fn poll(
                &self,
                timeout: OptionalOption,
                vm: &VirtualMachine,
            ) -> PyResult<Vec<PyObjectRef>> {
                let mut fds = self.fds.lock();
                let timeout_ms = match timeout.flatten() {
                    Some(ms) => {
                        let ms = if let Some(float) = ms.payload::<PyFloat>() {
                            float.to_f64().to_i32()
                        } else if let Some(int) = vm.to_index_opt(ms.clone()) {
                            int?.as_bigint().to_i32()
                        } else {
                            return Err(vm.new_type_error(format!(
                                "expected an int or float for duration, got {}",
                                ms.class()
                            )));
                        };
                        ms.ok_or_else(|| vm.new_value_error("value out of range".to_owned()))?
                    }
                    None => -1,
                };
                let timeout_ms = if timeout_ms < 0 { -1 } else { timeout_ms };
                let deadline = (timeout_ms >= 0)
                    .then(|| time::Instant::now() + time::Duration::from_millis(timeout_ms as u64));
                let mut poll_timeout = timeout_ms;
                loop {
                    let res = unsafe { libc::poll(fds.as_mut_ptr(), fds.len() as _, poll_timeout) };
                    let res = if res < 0 {
                        Err(std::io::Error::last_os_error())
                    } else {
                        Ok(())
                    };
                    match res {
                        Ok(()) => break,
                        Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {
                            vm.check_signals()?;
                            if let Some(d) = deadline {
                                match d.checked_duration_since(time::Instant::now()) {
                                    Some(remaining) => poll_timeout = remaining.as_millis() as i32,
                                    // we've timed out
                                    None => break,
                                }
                            }
                        }
                        Err(e) => return Err(e.into_pyexception(vm)),
                    }
                }
                Ok(fds
                    .iter()
                    .filter(|pfd| pfd.revents != 0)
                    .map(|pfd| (pfd.fd, pfd.revents & 0xfff).into_pyobject(vm))
                    .collect())
            }
        }
    }
}