use crate::transform::MirPass;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use rustc_target::spec::PanicStrategy;

pub struct SeparateConstSwitch;

impl<'tcx> MirPass<'tcx> for SeparateConstSwitch {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, _body: &mut Body<'tcx>) {
        // no-op pass for the sake of comparison
    }
}

pub fn no_landing_pads<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    if tcx.sess.panic_strategy() != PanicStrategy::Abort {
        return;
    }

    for block in body.basic_blocks_mut() {
        let terminator = block.terminator_mut();
        if let Some(unwind) = terminator.kind.unwind_mut() {
            unwind.take();
        }
    }
}
