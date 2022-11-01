include "../Types.dfy"

// Models an abstract track-addressible device that understands how the track geometry
// of the physical device is affected by reads and writes to the device.
//
// Things this has to do:
// Track validity
//
// Right now, this assumes that a write anywhere in a track invalidates the next track.
// This may either be too coarse (presumably the device could do it at the block level?
// or too fine (multiple tracks ought to be invalidated?)
//
module TrackedDisk {
    import opened NativeTypes
    import opened Types

    datatype Constants = Constants(
        drive_sz: uint64,
        zone_map: seq<Pair<uint32>>
    )

    datatype State = State(validTracks: set<uint32>)
    datatype Step =
    | ReadTrack(tid: uint32)
    | WriteTrack(tid: uint32)
    | Stutter

    predicate TrackInRange(c: Constants, tid: uint32) {
        exists i :: 0 <= i < |c.zone_map|
                 && c.zone_map[i].b >= tid 
                 && c.zone_map[i].e < tid 
    }

    predicate ValidStep(c: Constants, step: Step)
    {
        match step {
            case Stutter => true
            case ReadTrack(tid) => TrackInRange(c, tid)
            case WriteTrack(tid) => TrackInRange(c, tid)
        }
    }

    predicate NextRead(c: Constants, state: State, state': State, tid: uint32) 
    {
        tid in state.validTracks //TODO: or in state' ???
    }

    predicate NextWrite(c: Constants, state: State, state': State, tid: uint32) 
    {
        // XXX: hm, is this true?  Should we be dividing up the track space to
        // avoid this special case sooner?
        if tid == 0 then
        tid in state.validTracks else
        tid in state.validTracks && !(tid-1 in state.validTracks)
    }

    predicate NextStep(c: Constants, step: Step, state: State, state': State) 
        requires ValidStep(c, step)
    {
        match step {
            case Stutter => state == state'
            case ReadTrack(tid) => NextRead(c, state, state', tid)
            case WriteTrack(tid) => NextWrite(c, state, state', tid)
        }
    }

    predicate Next(c: Constants, state: State, state': State)
    {
        exists step :: ValidStep(c, step) && NextStep(c, step, state, state')
    }

}