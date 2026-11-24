# RustBelt POPL’18：不使用 Iris 的类型安全证明题

题目目录：[λRust 类型安全](rustbelt__lambda-rust__type-soundness)。

实验想看的是：只给 λRust 的核心语言、执行语义和类型规则，不给 Iris、lifetime logic 或原证明，agent 能不能在 Rocq 里自己找到证明路线？题目不要求重造 Iris。

## 题面怎么来的

执行语义沿用 `popl18` 版 [artifact 源码](https://github.com/kallydev/lambda-rust/tree/eec05e0aa61e2e8346ab380d0930bbaca4cc1a31)（固定版本镜像）。原 artifact 的 `typed_instruction` 和 `typed_body` 本身是用 Iris 的 weakest precondition 定义的，不能只删掉 `import`。因此，我们根据[论文技术附录](https://plv.mpi-sws.org/rustbelt/popl18/appendix.pdf)把核心类型规则重写成独立的 Rocq 判断。保留的是静态 lifetime 规则，拿掉的是用来证明它们安全的 lifetime logic。

| 文件 | 内容 |
| --- | --- |
| `Core.v` | 沿用原版的语法、值、堆、求值上下文和单步规则，包括原子操作、分两步执行的非原子操作和 `Fork`。把原来借用 Iris 接口定义的上下文归约和线程池归约直接写在 λRust 上，并保留原版的数据竞争定义。 |
| `Types.v` | 对应附录 §1.4 和 §§1.4.1–1.4.3：类型语法与良构性、递归类型和大小、Copy/Send/Sync，以及外部和局部 lifetime 上下文、lifetime 包含关系和存活条件。 |
| `Inclusion.v` | 对应附录 §1.4.4 和 §1.4.5 的读写类型规则：子类型、类型和 continuation 上下文的包含关系、积类型的拆分与合并、借用、共享、重借用，以及 lifetime 结束后恢复权限。 |
| `Surface.v` | 对应附录 §1.3 的 CPS 程序语法。展开到核心语言时，沿用 artifact 的 `new`、`delete`、`memcpy` 和调用展开；保留 lifetime 开始和结束时的执行步。 |
| `Typing.v` | 对应附录 §1.4.5 的指令和程序体类型规则，包括 continuation 的定义和跳转、lifetime 多态的程序及调用、lifetime 的等同与开始和结束，以及对拥有或借来的和类型做分支。 |
| `Task.v` | 目标是 `type_soundness_closed`。和原 artifact 一样，从空堆开始、使用同一个默认退出 continuation，证明每个可达状态都没有数据竞争，且每个线程要么是值、要么能继续执行。前提改为用语法类型规则说明入口程序类型正确，不依赖 Iris 断言。 |

Rocq 编码显式写出了类型变量的绑定、良构性和参数个数条件，并用带作用域的假设上下文表示递归子类型规则 `T-rec` 的前提。调用规则 `F_call` 要求返回值的形参不能捕获调用者保留的资源路径（包括字段路径和被 lifetime 暂时阻塞的资源）。函数的 lifetime 要求按附录显式给出，不使用原 artifact 的 `FP_wf` 自动补充。题面不提供内存不变量、类型的语义解释或安全性证明。

原版核心执行语义保留 `Fork`，但附录的核心类型规则不直接给 `Fork` 定型。像 `thread::spawn` 这样的接口是 RustBelt 另外验证的库。因此，这道题要求证明的是**闭合 λRust 核心**的类型安全，不包含对这些 `unsafe` 库的重新验证。

复用的执行定义保留原项目的 [BSD 许可证](LICENSE.rustbelt)；归约的通用定义来自同样采用 BSD 许可证的 Iris 接口。

## 怎么检查

使用 Rocq 9.1 和 stdpp 1.13.0。目标定理留空；如果只想编译题面定义，可以运行：

```bash
cd benchmarks/rustbelt-no-iris/rustbelt__lambda-rust__type-soundness/input
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq Typing.vo
```

[回归检查](checks/CoreExamples.v)不提供给模型，覆盖闭合入口程序、多态调用、递归子类型、借用与重借用、权限恢复等。目前这份编码没有参考证明，也尚未跑模型。检查提交时，除了编译，还应通过 `Print Assumptions type_soundness_closed.` 确认目标没有依赖公理，并另外核对其导入的库。
